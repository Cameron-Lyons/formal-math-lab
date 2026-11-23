#!/usr/bin/env python3
"""Count standard monomials using Python integers and a completed standard basis.

Input JSON format::

  {"format": "leading-monomial-ideal-v1", "variables": 2,
   "standard_basis_complete": true,
   "leading_monomials": [[3,0], [0,4], [1,2]], "provenance": {...}}

The completion flag is an attestation from the exporting backend, not a
standard-basis test performed here. This program must not receive the leading
monomials of an arbitrary polynomial generating set. For tests, monomial
generators themselves are always a standard basis of their monomial ideal.

No Singular vdim/hilb value, floating-point arithmetic, enumeration of all
monomials, or machine-sized count accumulator is used.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from math import prod
from pathlib import Path
import time


class MissingPurePowerBounds(ValueError):
    """The supplied leading ideal is not zero-dimensional."""


class CountLimitExceeded(RuntimeError):
    """A state limit was reached; no complete count is available."""


def _integer(value, name):
    if not isinstance(value,int) or isinstance(value,bool) or value < 0:
        raise ValueError(f'{name} must be a nonnegative integer')
    return value


def _validate(generators, variables, standard_basis_complete):
    if standard_basis_complete is not True:
        raise ValueError('A completed standard basis must be explicitly attested; '
                         'arbitrary polynomial generators cannot be counted this way.')
    generators = [tuple(row) for row in generators]
    if variables is None:
        if not generators:
            raise ValueError('variables is required when the generator list is empty')
        variables = len(generators[0])
    variables = _integer(variables,'variables')
    for row in generators:
        if len(row) != variables:
            raise ValueError('leading monomial vector length differs from variables')
        for exponent in row:
            _integer(exponent,'exponent')
    return variables,tuple(sorted(set(generators)))


def _initial_bounds(generators, variables):
    bounds = [None]*variables
    mixed = []
    for row in generators:
        support = [i for i,e in enumerate(row) if e]
        if not support:
            return None  # 1 belongs to the leading ideal: the quotient is zero.
        if len(support)==1:
            i = support[0]
            bounds[i] = row[i] if bounds[i] is None else min(bounds[i],row[i])
        else:
            mixed.append(row)
    missing = [i for i,bound in enumerate(bounds) if bound is None]
    if missing:
        raise MissingPurePowerBounds('No pure-power leading monomial bounds variables '
                                     + ','.join(map(str,missing)))
    return tuple(bounds),tuple(mixed)


class _Counter:
    def __init__(self, max_states):
        self.cache = {}
        self.max_states = max_states
        self.stats = dict(states=0,cache_hits=0,box_leaves=0,zero_leaves=0,
                          component_factorizations=0,interval_branches=0,
                          antichain_removed=0,max_depth=0)

    def normalize(self, bounds, generators):
        """Tighten pure bounds and reduce forbidden orthants to an antichain."""
        bounds = list(bounds)
        mixed = []
        for row in generators:
            support = [i for i,e in enumerate(row) if e]
            if not support:
                return None
            if len(support)==1:
                i = support[0]
                bounds[i] = min(bounds[i],row[i])
            else:
                mixed.append(row)
        # Bounds equal to one force exponent zero and contribute factor one.
        active = tuple(i for i,bound in enumerate(bounds) if bound > 1)
        rows = {tuple(row[i] for i in active) for row in mixed
                if all(e < bound for e,bound in zip(row,bounds))}
        bounds = tuple(bounds[i] for i in active)
        minimal = []
        sparse = []
        for row in sorted(rows,key=lambda row:(sum(row),row)):
            support_mask = sum(1 << i for i,e in enumerate(row) if e)
            dominated = False
            for mask,terms in sparse:
                if mask & ~support_mask == 0 and all(e <= row[i] for i,e in terms):
                    dominated = True
                    self.stats['antichain_removed'] += 1
                    break
            if not dominated:
                minimal.append(row)
                sparse.append((support_mask,tuple((i,e) for i,e in enumerate(row) if e)))
        return bounds,tuple(sorted(minimal))

    @staticmethod
    def components(generators, variables):
        parent = list(range(variables))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i

        used = set()
        for row in generators:
            support = [i for i,e in enumerate(row) if e]
            used.update(support)
            first = find(support[0])
            for i in support[1:]:
                parent[find(i)] = first
        groups = {}
        for i in sorted(used):
            groups.setdefault(find(i),[]).append(i)
        return list(groups.values()),set(range(variables))-used

    @staticmethod
    def branch_variable(generators, variables):
        # Prefer variables touching many generators per distinct threshold.
        # Compare these rational scores using integers, with stable tie breaks.
        best = None
        best_frequency,best_intervals = 0,1
        for i in range(variables):
            values = [row[i] for row in generators if row[i]]
            frequency,intervals = len(values),len(set(values))+1
            if (best is None or frequency*best_intervals > best_frequency*intervals
                    or (frequency*best_intervals == best_frequency*intervals
                        and frequency > best_frequency)):
                best,best_frequency,best_intervals = i,frequency,intervals
        return best

    def count(self, bounds, generators, depth=0):
        self.stats['max_depth'] = max(self.stats['max_depth'],depth)
        normalized = self.normalize(bounds,generators)
        if normalized is None:
            self.stats['zero_leaves'] += 1
            return 0
        bounds,generators = normalized
        key = bounds,generators
        if key in self.cache:
            self.stats['cache_hits'] += 1
            return self.cache[key]
        if self.max_states is not None and self.stats['states'] >= self.max_states:
            raise CountLimitExceeded(f'Exceeded {self.max_states} canonical states; no exact count.')
        self.stats['states'] += 1
        if not generators:
            self.stats['box_leaves'] += 1
            result = prod(bounds)
        else:
            components,isolated = self.components(generators,len(bounds))
            if len(components)>1 or isolated:
                self.stats['component_factorizations'] += 1
                result = prod(bounds[i] for i in isolated)
                for component in components:
                    subset = set(component)
                    local = [tuple(row[i] for i in component) for row in generators
                             if next(i for i,e in enumerate(row) if e) in subset]
                    result *= self.count(tuple(bounds[i] for i in component),local,depth+1)
                    if result == 0:
                        break
            else:
                variable = self.branch_variable(generators,len(bounds))
                cuts = sorted({0,bounds[variable]} | {row[variable] for row in generators})
                remaining = bounds[:variable]+bounds[variable+1:]
                result = 0
                for lower,upper in zip(cuts,cuts[1:]):
                    # A generator can divide a monomial in this interval iff
                    # its selected exponent is <= lower. Remove that coordinate
                    # and retain exactly those active generators.
                    projected = [row[:variable]+row[variable+1:] for row in generators
                                 if row[variable] <= lower]
                    self.stats['interval_branches'] += 1
                    result += (upper-lower)*self.count(remaining,projected,depth+1)
        self.cache[key] = result
        return result


def count_standard_monomials(leading_monomials, variables=None, *,
                             standard_basis_complete=False, max_states=None,
                             stats=None):
    """Return the exact finite staircase size as a Python int.

    Missing pure-power bounds raise MissingPurePowerBounds. A state budget raises
    CountLimitExceeded rather than returning a partial count. The caller must
    establish that the input really is a completed standard-basis leading ideal.
    """
    if max_states is not None and (_integer(max_states,'max_states') == 0):
        raise ValueError('max_states must be positive')
    variables,generators = _validate(leading_monomials,variables,standard_basis_complete)
    initial = _initial_bounds(generators,variables)
    counter = _Counter(max_states)
    answer = 0 if initial is None else counter.count(*initial)
    if stats is not None:
        stats.update(counter.stats)
        stats.update(variables=variables,input_generators=len(generators),
                     cached_states=len(counter.cache),count_bit_length=answer.bit_length(),
                     unit_ideal=initial is None)
    return answer


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--max-states',type=int)
    args = parser.parse_args()
    raw = args.input.read_bytes()
    document = json.loads(raw)
    if document.get('format') != 'leading-monomial-ideal-v1':
        parser.error('unsupported leading-monomial JSON format')
    started = time.monotonic()
    stats = {}
    try:
        count = count_standard_monomials(document['leading_monomials'],document['variables'],
                    standard_basis_complete=document.get('standard_basis_complete',False),
                    max_states=args.max_states,stats=stats)
    except (ValueError,CountLimitExceeded) as error:
        parser.error(str(error))
    result = dict(status='complete',dimension_decimal=str(count),
                  arithmetic='Python arbitrary-precision integer',
                  standard_basis_complete=True,input=str(args.input.resolve()),
                  input_sha256=hashlib.sha256(raw).hexdigest(),
                  wall_seconds=round(time.monotonic()-started,6),stats=stats,
                  source_provenance=document.get('provenance'))
    text = json.dumps(result,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')


if __name__ == '__main__':
    main()

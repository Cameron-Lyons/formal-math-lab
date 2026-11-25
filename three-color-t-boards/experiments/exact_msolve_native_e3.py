#!/usr/bin/env python3
"""Append four exact role-histogram cubics in natural F3 coordinates."""
import hashlib
import json
from pathlib import Path

SOURCE = Path(__file__).resolve().parent/'exact_f3_math_e3_constraints.json'
SOURCE_SHA256 = '6cef0fb4e6b3ccb80f17f7aebadfd02fd777d082e1dedb84cdf5d9786d408392'
MODEL_SHA256 = 'fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4'
LABELS = ['e3:T', 'e3:T:M', 'e3:M:L', 'e3:M:R']
COUNTS = [158, 180, 86, 150]


def augment(source, metadata):
    if (metadata.get('prime') != 3 or metadata.get('variables') != 96 or
            metadata.get('ternary_native_field') is not True or
            metadata.get('native_field_source_sha256') != MODEL_SHA256 or
            metadata.get('field_domain_equations') != 96 or
            metadata.get('retained_moment_equations') != 76 or
            metadata.get('retained_unary_quadratic_moments') != 4 or
            metadata.get('prefix') != '' or metadata.get('count_divisor') != 1 or
            metadata.get('count_multiplier') != 1):
        raise ValueError('native e3 requires the complete unrestricted natural-F3 base')
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise ValueError('native e3 source changed; independent review required')
    data = json.loads(raw)
    if (data['format'] != 't-board-natural-f3-e3-augmentation-v1' or
            data['native_source_sha256'] != MODEL_SHA256 or
            data['free_prefix_variables'] != metadata['free_prefix_variables'] or
            data['original_cell_order'] != metadata['original_cell_order'] or
            [e['label'] for e in data['equations']] != LABELS):
        raise ValueError('native e3 source coordinates or labels mismatch')
    polynomials = []
    for equation, count in zip(data['equations'], COUNTS):
        pieces, seen = [], set()
        if len(equation['terms']) != count:
            raise ValueError('native e3 term count mismatch')
        for coefficient, encoded in equation['terms']:
            word = int(encoded, 16)
            if coefficient not in (1, 2) or word < 0 or word >> (4*96) or word in seen:
                raise ValueError('invalid native e3 term')
            seen.add(word)
            powers = [(word >> (4*i)) & 15 for i in range(96)]
            if sum(powers) != 3 or any(e > 2 for e in powers):
                raise ValueError('expected reduced ordinary cubic monomial')
            factors = [f'x{i+1}' + (f'^{e}' if e != 1 else '')
                       for i,e in enumerate(powers) if e]
            pieces.append(('2*' if coefficient == 2 else '')+'*'.join(factors))
        polynomials.append('+'.join(pieces))
    augmented = source.rstrip('\n')+',\n'+',\n'.join(polynomials)+'\n'
    result = dict(metadata)
    result.update(native_e3=True, native_e3_generators=4, generators=metadata['generators']+4,
                  equation_labels=metadata['equation_labels']+LABELS,
                  native_e3_source=str(SOURCE), native_e3_source_sha256=SOURCE_SHA256,
                  native_e3_adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  pre_e3_input_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  input_sha256=hashlib.sha256(augmented.encode()).hexdigest(),
                  native_e3_scope='redundant role cubics; unrestricted count unchanged')
    return augmented, result

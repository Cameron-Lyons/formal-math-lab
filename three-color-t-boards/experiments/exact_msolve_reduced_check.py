#!/usr/bin/env python3
"""Focused checks of reduced msolve export, with no solver invocation."""
from copy import deepcopy
import itertools
import json
from pathlib import Path
import re

import exact_msolve_reduced as exporter


def parse_word(term):
    if term == '1':
        return 0
    result = 0
    seen = set()
    for factor in term.split('*'):
        match = re.fullmatch(r'x([1-9]\d*)(?:\^([12]))?', factor)
        assert match, factor
        variable, exponent = int(match[1])-1, int(match[2] or 1)
        assert 0 <= variable < 96 and variable not in seen
        seen.add(variable)
        result |= exponent << (2*variable)
    return result


def main():
    rejected = []
    def refuses(name, function):
        try:
            function()
        except ValueError:
            rejected.append(name)
        else:
            raise AssertionError('accepted invalid data: '+name)
    for name, term in [('exponent-three', '0x3'), ('highest-exponent-three', hex(3 << 190)),
                       ('overflow', hex(1 << 192)), ('negative', '-0x1'), ('missing-prefix', '1'),
                       ('invalid-hex', '0xz'), ('whitespace', ' 0x1'), ('empty', '0x'),
                       ('integer', 1), ('boolean', True)]:
        refuses(name, lambda term=term: exporter.decode_monomial(term))
    refuses('duplicate-word', lambda: exporter.decode_polynomial(['0x1', '0x1']))
    refuses('duplicate-numeric-alias', lambda: exporter.decode_polynomial(['0x1', '0x01']))
    refuses('duplicate-constant', lambda: exporter.decode_polynomial(['0x0', '0x00']))
    refuses('zero-polynomial', lambda: exporter.decode_polynomial([]))
    refuses('nonboolean-mode', lambda: exporter.reduced_definitions(1))
    refuses('duplicate-json-key', lambda: json.loads('{"variables":96,"variables":95}', object_pairs_hook=exporter.unique_object))
    assert exporter.decode_monomial('0x0') == 0
    assert exporter.decode_monomial(hex(2 << 190)) == 2 << 190
    assert exporter.monomial_text(0) == '1'
    source = json.loads(exporter.SOURCE.read_bytes())
    for name, mutate in (
            ('missing-pivot-domain', lambda data: data['remaining_equations'].pop()),
            ('duplicate-equation', lambda data: data['remaining_equations'].__setitem__(-1, data['remaining_equations'][0])),
            ('wrong-field', lambda data: data.update(coefficient_field='F4')),
            ('wrong-variables', lambda data: data.update(variables=95)),
            ('missing-free-domains', lambda data: data.update(free_domain_equations='')),
            ('wrong-free-map', lambda data: data['free_original_cells'].__setitem__(0, 0)),
            ('missing-pivot-substitution', lambda data: data['pivot_substitutions'].pop('99')),
            ('duplicate-substitution-term', lambda data: data['pivot_substitutions']['0'].append(data['pivot_substitutions']['0'][0])),
            ('lost-term', lambda data: data['remaining_equations'][0]['terms'].pop())):
        changed = deepcopy(source); mutate(changed)
        refuses(name, lambda changed=changed: exporter.validate_document(changed))
    default_text, default_meta = exporter.reduced_definitions()
    all_text, all_meta = exporter.reduced_definitions(True)
    default_lines, all_lines = default_text.splitlines(), all_text.splitlines()
    assert default_lines[:2] == all_lines[:2]
    default_polynomials = [line.rstrip(',') for line in default_lines[2:]]
    all_polynomials = [line.rstrip(',') for line in all_lines[2:]]
    assert len(default_polynomials) == 136 and len(all_polynomials) == 172
    assert all_polynomials[:136] == default_polynomials
    assert default_polynomials[:96] == [f'x{i+1}^3+1' for i in range(96)]
    decoded = [tuple(parse_word(term) for term in polynomial.split('+'))
               for polynomial in all_polynomials[96:]]
    assert sum(map(len, decoded[:40])) == 25070 and sum(map(len, decoded)) == 36954
    original = {equation['label']: tuple(int(word, 16) for word in equation['terms'])
                for equation in source['remaining_equations']}
    exported = dict(zip(all_meta['equation_labels'], decoded))
    for label, words in original.items():
        assert exported[label] == words
    for label, words in original.items():
        if label.startswith('moment:'):
            exponents = list(map(int, label.split(':')[1].split(',')))
            partner = 'moment:'+','.join(str(2*e % 3) for e in exponents)
            # Independent exponent arithmetic, not the helper's transform.
            expected = {sum((0 if (e := (word >> (2*i) & 3)) == 0 else 3-e) << (2*i)
                            for i in range(96)) for word in words}
            assert set(exported[partner]) == expected and len(exported[partner]) == len(words)
    square_tests = 0
    for exponents in itertools.product(range(3), repeat=5):
        word = sum(e << (2*i) for i, e in enumerate(exponents))
        squared = exporter.frobenius_word(word, 5)
        assert [(squared >> (2*i)) & 3 for i in range(5)] == [2*e % 3 for e in exponents]
        assert exporter.frobenius_word(squared, 5) == word
        square_tests += 1
    for name, text, metadata in (('40', default_text, default_meta), ('80', all_text, all_meta)):
        path = exporter.ROOT/f'exact_msolve_reduced_{name}.ms'
        path.write_text(text)
        path.with_suffix('.json').write_text(json.dumps(metadata, indent=2)+'\n')
        assert metadata['count_divisor'] == 1 and metadata['prefix'] == ''
        assert metadata['substituted_pivot_domain_equations'] == 4
    report = dict(status='PASS', modes={
        '40': dict(variables=96, generators=136, terms_outside_free_domains=25070,
                   input_sha256=default_meta['input_sha256']),
        '80': dict(variables=96, generators=172, terms_outside_free_domains=36954,
                   input_sha256=all_meta['input_sha256'])},
        strict_rejections=rejected, frobenius_small_monomial_checks=square_tests,
        all_default_polynomials_preserved=True, pivot_domains_retained=4,
        count_divisor=1, fixed_prefix='', source_sha256=default_meta['source_sha256'],
        solver_processes_started=0)
    (exporter.ROOT/'exact_msolve_reduced_checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()

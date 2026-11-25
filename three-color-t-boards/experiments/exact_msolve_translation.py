#!/usr/bin/env python3
"""Export the full F3 count with the apex color as an independent factor."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE/'exact_f3_translation_model.json'
BASE_SHA256 = '1e2dc884f8996c6bd1b5093f24fa6fe7d7f1002e97b69762baadfda5adf94a7f'
EXTRA = HERE/'exact_f3_translation_e3_constraints.json'
EXTRA_SHA256 = '5bed48f4a1523c26d02a2add9423c463ffdb08af5cf5ecf7bab40a0cceae4a40'
INPUT_SHA256 = {False:'339f10f7632c231f4e79a0b5c1e99700798fe7726c3b359ab097611ee650d3b1',
                True:'44e74446e0971a06a40d89fc18446d33e3355d3ef6e42b4197e3ac0686defee5'}


def translation_definitions(e3=False):
    if type(e3) is not bool:
        raise ValueError('translation augmentation option must be Boolean')
    raw = BASE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != BASE_SHA256:
        raise ValueError('translation model changed; independent review required')
    data = json.loads(raw)
    if (data['format'] != 't-board-natural-f3-translation-v1' or
            data['variables'] != 96 or data['coefficient_characteristic'] != 3 or
            data['coupled_variables'] != 95 or data['offset_variable_index'] != 95 or
            data['extension_variable'] or data['prefix'] or data['fixed_original_cells'] or
            data['symmetry_normalization'] or data['count_divisor'] != 1 or
            data['count_multiplier'] != 1 or len(data['domain_equations']) != 96 or
            len(data['moment_equations']) != 76):
        raise ValueError('translation model must retain the full independent three-color factor')
    equations = data['domain_equations']+data['moment_equations']
    if e3:
        raw_extra = EXTRA.read_bytes()
        if hashlib.sha256(raw_extra).hexdigest() != EXTRA_SHA256:
            raise ValueError('translated e3 source changed; independent review required')
        extra = json.loads(raw_extra)
        if (extra['source_translation_model_sha256'] != BASE_SHA256 or
                extra['free_normalized_prefix_variables'] != data['free_normalized_prefix_variables'] or
                extra['offset_variable_index'] != 95 or len(extra['equations']) != 4):
            raise ValueError('translated e3 coordinate mismatch')
        equations += extra['equations']
    polynomials = []
    for number, equation in enumerate(equations):
        pieces, seen = [], set()
        for coefficient, encoded in equation['terms']:
            word = int(encoded, 16)
            if coefficient not in (1, 2) or word < 0 or word >> (4*96) or word in seen:
                raise ValueError('invalid translated coefficient or exponent encoding')
            seen.add(word)
            powers = [(word >> (4*i)) & 15 for i in range(96)]
            if any(e > 3 for e in powers) or (number >= 96 and powers[95]):
                raise ValueError('unexpected exponent or coupled apex-color variable')
            factors = [f'x{i+1}'+(f'^{e}' if e != 1 else '') for i,e in enumerate(powers) if e]
            pieces.append((str(coefficient)+'*' if coefficient != 1 and factors else '')+
                          ('*'.join(factors) if factors else str(coefficient)))
        if not pieces:
            raise ValueError('zero retained translated equation')
        polynomials.append('+'.join(pieces))
    if polynomials[95] != '2*x96+x96^3':
        raise ValueError('independent apex-color field domain must remain present')
    source = ','.join(f'x{i+1}' for i in range(96))+'\n3\n'+',\n'.join(polynomials)+'\n'
    digest = hashlib.sha256(source.encode()).hexdigest()
    if digest != INPUT_SHA256[e3]:
        raise ValueError('translation input differs from the frozen serialization')
    metadata = dict(model='ternary-native-field-f3-translation', mode='all-80-power-moments',
                    variables=96, prime=3, field='F3', ring_type='ordinary polynomial ring',
                    color_values=[0,1,2], scope='full labeled ternary boards',
                    count_scope='full labeled boards', count_divisor=1, count_multiplier=1,
                    prefix='', fixed_prefix_rows=0, fixed_cell_count=0, fixed_original_cells=[],
                    symmetry_normalization=False, extension_variable=False,
                    ternary_native_field=True, native_translation=True, native_e3=e3,
                    generators=len(equations), field_domain_equations=96,
                    coupled_variables=95, offset_variable_index=95,
                    offset_semantics=data['offset_semantics'], independent_offset_domain='x96^3-x96',
                    substituted_pivot_domain_equations=0, moment_equations=80,
                    retained_moment_equations=76, eliminated_linear_moments=4,
                    retained_unary_quadratic_moments=4,
                    original_cell_order=data['original_cell_order'],
                    free_normalized_prefix_variables=data['free_normalized_prefix_variables'],
                    normalized_color_linear_forms=data['normalized_color_linear_forms'],
                    original_color_linear_forms=data['original_color_linear_forms'],
                    equation_labels=[e['label'] for e in equations], source=str(BASE),
                    source_sha256=BASE_SHA256, native_field_source_sha256=BASE_SHA256,
                    translation_source_sha256=BASE_SHA256,
                    untranslated_source_sha256=data['source_native_model_sha256'],
                    source_format=data['format'],
                    translation_exporter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    input_sha256=digest, status='PREPARED_NOT_RUN', standard_basis_complete=False)
    if e3:
        metadata.update(native_e3_generators=4, native_e3_source=str(EXTRA),
                        native_e3_source_sha256=EXTRA_SHA256, pre_e3_input_sha256=INPUT_SHA256[False])
    return source, metadata

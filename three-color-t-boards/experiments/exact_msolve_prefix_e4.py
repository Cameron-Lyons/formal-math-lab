#!/usr/bin/env python3
"""Append four audited ordinary quartics to the exact prefix-coordinate model."""
import hashlib
import json
from pathlib import Path

SOURCE = Path(__file__).resolve().parent/'exact_pivot_math_prefix_e4_constraints.json'
SOURCE_SHA256 = 'dadaa5f4caf17b00311abe9000cf5463e101946bfc0ab9b2fb319f26838e8a91'
MODEL_SHA256 = '7f8251ab52e8d6869c19cc861dc98b0c1e66904313b0d87920d9f95659700092'
LABELS = ['e4:T', 'e4:T:M', 'e4:M:L', 'e4:M:R']
TERM_COUNTS = [12324, 1146, 278, 446]


def augment(source, metadata):
    if (metadata.get('prime') != 2 or metadata.get('variables') != 96 or
            metadata.get('ternary_prefix_sums') is not True or
            metadata.get('histogram_e2') is not True or
            metadata.get('prefix_model_source_sha256') != MODEL_SHA256 or
            metadata.get('count_divisor') != 1 or metadata.get('count_multiplier') != 1 or
            metadata.get('prefix') != '' or metadata.get('transformed_original_cubic_domains') != 100):
        raise ValueError('e4 augmentation requires the unrestricted prefix model with its e2 equations')
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA256:
        raise ValueError('e4 source changed; independent audit required')
    data = json.loads(raw)
    if (data['format'] != 't-board-prefix-e4-augmentation-v1' or
            data['prefix_source_sha256'] != MODEL_SHA256 or
            data['free_prefix_variables'] != metadata['free_prefix_variables'] or
            data['original_cell_order'] != metadata['original_cell_order'] or
            data['variables'] != 96 or data['coefficient_characteristic'] != 2 or
            [eq['label'] for eq in data['equations']] != LABELS or
            not set(data['required_e2_labels']).issubset(metadata['equation_labels'])):
        raise ValueError('e4 model, coordinate map, or prerequisites mismatch')
    polynomials = []
    for equation, expected_terms in zip(data['equations'], TERM_COUNTS):
        words = [int(term, 16) for term in equation['terms']]
        if len(words) != expected_terms or len(set(words)) != expected_terms:
            raise ValueError('e4 support size or uniqueness mismatch')
        pieces = []
        for word in words:
            if word < 0 or word >> (4*96):
                raise ValueError('e4 monomial exceeds ordinary ring')
            exponents = [(word >> (4*i)) & 15 for i in range(96)]
            if sum(exponents) != 4:
                raise ValueError('expected ordinary quartic monomial')
            factors = [f'x{i+1}' + (f'^{e}' if e != 1 else '')
                       for i, e in enumerate(exponents) if e]
            pieces.append('*'.join(factors))
        polynomials.append('+'.join(pieces))
    augmented = source.rstrip('\n')+',\n'+',\n'.join(polynomials)+'\n'
    result = dict(metadata)
    result.update(histogram_e4=True, elementary_e4_generators=4,
                  generators=metadata['generators']+4,
                  equation_labels=metadata['equation_labels']+LABELS,
                  elementary_e4_source=str(SOURCE), elementary_e4_source_sha256=SOURCE_SHA256,
                  elementary_e4_adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  pre_e4_input_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  input_sha256=hashlib.sha256(augmented.encode()).hexdigest(),
                  elementary_e4_scope='redundant role quartics; unrestricted count unchanged')
    return augmented, result

#!/usr/bin/env python3
"""Append audited, redundant characteristic-two color-balance equations."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
HASHES = {
    'original': 'b24731564028877b8dd39850334b80810b776e271a064b89b46fd6b25f59782f',
    'reduced': '4f8f351f5d11c27afc0b80b36c180e6f12fa7a90632eea2a709a0dae77a54d61',
}


def augment(text, metadata, *, reduced):
    if metadata['prime'] != 2 or metadata.get('prefix') or metadata['count_divisor'] != 1:
        raise ValueError('elementary augmentation requires unrestricted F2 board scope')
    kind = 'reduced' if reduced else 'original'
    path = ROOT / f'exact_parity_math_elementary_{kind}.json'
    raw = path.read_bytes()
    source_hash = hashlib.sha256(raw).hexdigest()
    if source_hash != HASHES[kind]:
        raise ValueError('elementary source changed; independent review required')
    data = json.loads(raw)
    n = metadata['variables']
    order = metadata.get('variable_original_cells', metadata.get('free_original_cells'))
    cells = data['free_original_cells']
    if (data['format'] != 't-board-elementary-augmentation-v1' or
            data['coefficient_field'] != 'F2' or data['variables'] != n or
            not isinstance(order, list) or len(set(order)) != n or
            set(order) != set(cells) or len(cells) != n or
            len(data['remaining_equations']) != 8):
        raise ValueError('elementary input shape or cell map mismatch')
    positions = {cell:i for i,cell in enumerate(order)}
    polynomials = []
    for equation in data['remaining_equations']:
        words = [int(term,16) for term in equation['terms']]
        if not words or len(set(words)) != len(words):
            raise ValueError('empty or duplicate elementary polynomial terms')
        pieces = []
        for word in words:
            if word < 0 or word >> (2*n):
                raise ValueError('elementary monomial exceeds ring')
            powers = [0]*n
            for old,cell in enumerate(cells):
                exponent = word >> (2*old) & 3
                if exponent == 3:
                    raise ValueError('invalid packed elementary exponent')
                powers[positions[cell]] = exponent
            factors = [f'x{i+1}'+(f'^{e}' if e != 1 else '')
                       for i,e in enumerate(powers) if e]
            pieces.append('*'.join(factors) or '1')
        polynomials.append('+'.join(pieces))
    result = text.rstrip('\n')+',\n'+',\n'.join(polynomials)+'\n'
    metadata = dict(metadata)
    metadata.update(histogram_e2=True, elementary_generators=8,
                    generators=metadata['generators']+8,
                    elementary_source=str(path), elementary_source_sha256=source_hash,
                    elementary_adapter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                    elementary_generator_labels=[e['label'] for e in data['remaining_equations']],
                    elementary_scope='redundant constraints; unrestricted count unchanged')
    # The reduced base exporter records its own input hash. Keep that provenance
    # distinct from the hash of the newly augmented input.
    if 'input_sha256' in metadata:
        metadata['base_input_sha256'] = metadata['input_sha256']
        metadata['input_sha256'] = hashlib.sha256(result.encode()).hexdigest()
    return result, metadata

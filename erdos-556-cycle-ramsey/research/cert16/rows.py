"""Generate binary extension certificates and their Lean proof obligations."""
from hashlib import sha256
from pathlib import Path
import struct
import sys

from tables import read_rows


def merge(ranges):
    """Join consecutive interval proofs in a balanced term."""
    if len(ranges) == 1:
        return ranges[0]
    middle = len(ranges) // 2
    return f'(joinRanges {merge(ranges[:middle])} {merge(ranges[middle:])})'


def pack(rows, destinations, order):
    """Split rows by estimated work to bound the cache of each kernel reduction."""
    data = bytearray()
    chunks = []
    first, offset, cost = 0, 0, 0
    budget = 4000 if order >= 8 else 18000
    for i, (graph, paths, moves) in enumerate(rows):
        data += graph.to_bytes(16, 'little') + struct.pack('<H', len(paths))
        for path in paths:
            data += struct.pack('<I', path)
        data += struct.pack('<I', len(moves))
        # The maskSet checker inserts the neighbors with the least mask first.
        for mask, index, perm in reversed(moves):
            data += struct.pack('<HH', mask, index)
            data += destinations[index].to_bytes(16, 'little') + struct.pack('<Q', perm)
        cost += len(paths) * 8 + len(moves) * order * (order + 1) // 2 + 30
        if cost >= budget or i + 1 - first >= 32 or i + 1 == len(rows):
            chunks.append((first, i + 1, offset))
            first, offset, cost = i + 1, len(data), 0
    return data, chunks


def write_strip(source, order, strip, chunks, digest):
    lower, upper = chunks[0][0], chunks[-1][1]
    out = ['import Ramsey556.Cert16.Read', 'import Ramsey556.Cert16.Ranges']
    if order > 1:
        out.append(f'import Ramsey556.Cert16.Layers.N{order - 1:02d}')
    out += ['', f'-- Generated from N{order:02d}.bin, SHA-256 {digest}.']
    out += ['', 'namespace Ramsey556.Cert16', '', 'set_option maxRecDepth 65536',
            'set_option maxHeartbeats 0', '']
    if order >= 7:
        out += ['set_option Elab.async false', '']
    modifier = 'noncomputable ' if order >= 8 else ''

    for first, end, offset in chunks:
        name = f'row{order}_{first}'
        check = f'check{order}_{first}'
        proof = f'good{order}_{first}'
        out += [
            f'private {modifier}def {name} : List Row := cert16Rows% "../Data/N{order:02d}.bin" {offset} {end-first}',
            f'private theorem {check} : checkChunk {order} (table {order}) (table {order+1}) {first} {name} = true := by decide +kernel',
            f'private theorem {proof} : GoodRange {order} {first} {end} :=',
            f'  chunk_sound {order} _ _ {first} {name} {check}', '',
        ]
    name = f'range{order}_{strip}'
    out += [f'theorem {name} : GoodRange {order} {lower} {upper} :=',
            '  ' + merge([f'good{order}_{first}' for first, _, _ in chunks]),
            '', 'end Ramsey556.Cert16', '']
    (source / f'N{order:02d}S{strip}.lean').write_text('\n'.join(out))
    return name


def main():
    root, destination = map(Path, sys.argv[1:])
    source, data = destination / 'Layers', destination / 'Data'
    source.mkdir(exist_ok=True)
    data.mkdir(exist_ok=True)
    for order in range(1, 16):
        rows = list(read_rows(root, order))
        targets = [row[0] for row in read_rows(root, order + 1)]
        raw, chunks = pack(rows, targets, order)
        (data / f'N{order:02d}.bin').write_bytes(raw)
        digest = sha256(raw).hexdigest()
        strips = min(4, len(chunks))
        proofs = []
        for strip in range(strips):
            first, end = len(chunks)*strip//strips, len(chunks)*(strip+1)//strips
            proofs.append(write_strip(source, order, strip, chunks[first:end], digest))
        out = [f'import Ramsey556.Cert16.Layers.N{order:02d}S{i}' for i in range(strips)]
        out += ['', 'namespace Ramsey556.Cert16', '',
                f'theorem rows{order} : ∀ i, i < (table {order}).size → RowGood {order} ((table {order}).get i) (table {order+1}) :=',
                f'  fun i hi => (show GoodRange {order} 0 {len(rows)} from {merge(proofs)}) i (Nat.zero_le i) hi',
                '', 'end Ramsey556.Cert16', '']
        (source / f'N{order:02d}.lean').write_text('\n'.join(out))
    (destination / 'Rows.lean').write_text('import Ramsey556.Cert16.Layers.N15\n')


if __name__ == '__main__':
    main()

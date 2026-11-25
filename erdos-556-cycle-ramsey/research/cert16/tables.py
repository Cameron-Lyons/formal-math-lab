"""Pack triangular graph codes into random-access Lean tables."""

import sys
from pathlib import Path


def read_rows(root, order):
    lines = (root / f"witness{order}.txt").read_text().splitlines()
    stride = 2 if order == 16 else 3
    for start in range(0, len(lines), stride):
        graph = int(lines[start])
        if order == 16:
            yield graph, int(lines[start + 1]), []
        else:
            paths = list(map(int, lines[start + 1].split()))
            entries = list(map(int, lines[start + 2].split()))
            moves = list(zip(entries[::3], entries[1::3], entries[2::3], strict=True))
            yield graph, paths, moves


def main():
    root, destination = map(Path, sys.argv[1:])
    out = [
        "import Ramsey556.Cert16.Check",
        "",
        "namespace Ramsey556.Cert16",
        "",
        "-- Generated catalog of 16-vertex density prefixes. Each input row is verified.",
    ]
    for order in range(1, 17):
        graphs = [row[0] for row in read_rows(root, order)]
        chunks = [
            hex(sum(graph << (128 * j) for j, graph in enumerate(graphs[i : i + 32])))
            for i in range(0, len(graphs), 32)
        ]
        out += [
            f"private def table{order} : Table := ⟨{len(graphs)}, #[",
            ",\n".join(chunks) + "]⟩",
            "",
        ]
    out += ["def table : Nat → Table"]
    out += [f"  | {order} => table{order}" for order in range(1, 17)]
    out += ["  | _ => ⟨0,#[]⟩", "", "end Ramsey556.Cert16", ""]
    destination.write_text("\n".join(out))


if __name__ == "__main__":
    main()

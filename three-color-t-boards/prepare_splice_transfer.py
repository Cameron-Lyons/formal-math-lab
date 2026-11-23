"""Discover or regenerate splice groups that reuse selected previously certified tails."""
import argparse
from collections import defaultdict
from itertools import permutations
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from prepare_splice import lean_list, pattern_codes, split_rows


ROOT = Path(__file__).resolve().parent
SOURCE_MODULES = {"splice_witnesses": "SpliceData", "splice_extension": "SpliceExtensionData"}
GROUPS_PER_MODULE = 8


def expand_transfer(data, sources):
    """Resolve relative skip counts against the original ordered tail lists."""
    if data["cut"] != 5:
        raise ValueError("expected a row-five transfer")
    groups = []
    for entry in data["groups"]:
        certificate = sources[entry["source"]]
        index = entry["index"]
        if certificate["cut"] != 5 or type(index) is not int or not 0 <= index < len(certificate["groups"]):
            raise ValueError("invalid transfer source group")
        original = certificate["groups"][index]["tails"]
        cursor = 0
        tails = []
        for gap in entry["gaps"]:
            if type(gap) is not int or gap < 0 or cursor + gap >= len(original):
                raise ValueError("invalid transfer tail selection")
            cursor += gap
            tails.append(original[cursor])
            cursor += 1
        if not tails:
            raise ValueError("empty transfer")
        groups.append({"pivot": entry["pivot"], "caps": entry["caps"], "tails": tails})
    return {"cut": 5, "groups": groups}


def signature(cap, pivot):
    codes = pattern_codes(split_rows(cap + pivot, 0, 6))
    return pivot, sum(1 << code for code in codes)


def cap_images(cap, pivot):
    rows = split_rows(cap + pivot, 0, 6)
    for colors in permutations("012"):
        table = str.maketrans("012", "".join(colors))
        for reflected in (False, True):
            yield "".join((row[::-1] if reflected else row).translate(table) for row in rows)


def discover_transfer(sources):
    # Previous explicit layers may contain later groups with the same signature.
    known = {signature(g["caps"][0], g["pivot"]) for s in sources.values() for g in s["groups"]}
    seen_prefix = {}
    for s in sources.values():
        for g in s["groups"]:
            for cap in g["caps"]:
                for action, value in enumerate(cap_images(cap, g["pivot"])):
                    if seen_prefix.setdefault(value, action) != action:
                        raise ValueError("prior prefixes do not distinguish symmetry actions")

    # All tails of a source with the same first row use the same 36 codes above
    # that row. Do the reverse enumeration only once for each first row.
    inputs, owners, first_indices = [], [], {}
    for source in SOURCE_MODULES:
        for index, group in enumerate(sources[source]["groups"]):
            owner = source, index
            positions = defaultdict(list)
            for j, tail in enumerate(group["tails"]):
                positions[tail[:13]].append(j)
            first_indices[owner] = positions
            for first in positions:
                inputs.append(f"{len(owners)} {group['caps'][0]}{group['pivot']}{first}\n")
                owners.append((owner, first))
    with TemporaryDirectory() as work:
        exe = Path(work) / "reverse"
        subprocess.run(["c++", "-O3", "-std=c++20", ROOT / "search_splice_transfer.cpp", "-o", exe], check=True)
        result = subprocess.run([exe], input="".join(inputs), text=True, stdout=subprocess.PIPE, check=True)
    caps = defaultdict(set)
    matches = defaultdict(lambda: defaultdict(set))
    for line in result.stdout.splitlines():
        witness, prefix = line.split()
        cap, pivot = prefix[:25], prefix[25:]
        key = signature(cap, pivot)
        if key not in known:
            owner, first = owners[int(witness)]
            caps[key].add(cap)
            matches[key][owner].add(first)
    candidates = []
    for key, by_owner in matches.items():
        # A single source keeps the inherited order. Pick the source supplying
        # the most tails when the same target can be reached more than one way.
        choices = []
        for owner, starts in by_owner.items():
            indices = sorted(j for first in starts for j in first_indices[owner][first])
            choices.append((len(indices), owner, indices))
        _, (source, index), indices = max(choices)
        candidates.append((len(indices)*len(caps[key]), key, source, index, indices))
    groups = []
    for _, (pivot, mask), source, index, indices in sorted(candidates, reverse=True):
        retained = []
        for cap in sorted(caps[pivot, mask]):
            images = list(cap_images(cap, pivot))
            if len(set(images)) != 12 or any(seen_prefix.get(x, i) != i for i, x in enumerate(images)):
                continue
            seen_prefix.update((x, i) for i, x in enumerate(images))
            retained.append(cap)
        if retained:
            gaps = [j - prev - 1 for prev, j in zip([-1] + indices, indices)]
            groups.append({"pivot": pivot, "caps": retained, "source": source, "index": index, "gaps": gaps})
    return {"cut": 5, "groups": groups}


def write_source(path, imports, body):
    contents = "\n".join("import " + s for s in imports) + """

-- Generated by prepare_splice_transfer.py from splice_transfer.json.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.SpliceTransferData
open Splice

""" + "\n".join(body) + "\nend TBoards.SpliceTransferData\n"
    if not path.exists() or path.read_text() != contents:
        path.write_text(contents)


def generate_transfer(data, sources, directory):
    resolved = expand_transfer(data, sources)
    dest = directory / "SpliceTransferData"
    dest.mkdir(parents=True, exist_ok=True)
    parts, all_names, all_sizes = [], [], []
    entries = data["groups"]
    if not entries:
        raise ValueError("empty transfer family")
    for start in range(0, len(entries), GROUPS_PER_MODULE):
        part = f"Part{len(parts):03}"
        imports = ["SpliceTransfer", *SOURCE_MODULES.values()] if len(parts) < 2 else [parts[-2]]
        body = []
        for number in range(start, min(start + GROUPS_PER_MODULE, len(entries))):
            entry, group = entries[number], resolved["groups"][number]
            name, template = f"group{number}", f"template{number}"
            old = f"{SOURCE_MODULES[entry['source']]}.group{entry['index']}"
            pivot = group['pivot']
            upper = signature(group['caps'][0], pivot)[1]
            lower = (1 << 81) - 1 - upper
            size = len(group['caps']) * len(group['tails'])
            caps = lean_list(int(cap, 3) for cap in group["caps"])
            body += [
                f"private def {template} : Group where", "  k := 5", f"  pivot := {lean_list(pivot)}",
                f"  caps := ({caps} : List Nat).map Packed.cap", "  tails := []",
                f"  upperMask := {upper}", f"  lowerMask := {lower}",
                f"private def selection{number} : List Nat := {lean_list(entry['gaps'])}", "",
                f"def {name} := Transfer.assemble {old} {template} selection{number}",
                f"theorem {name}_checked : {name}.Checked := by",
                f"  apply Transfer.assemble_checked _ _ _ {old}_checked <;> decide +kernel",
                f"theorem {name}_size : {name}.size = {size} := by decide +kernel", "",
            ]
            all_names.append(name)
            all_sizes.append(size)
        write_source(dest / f"{part}.lean", imports, body)
        parts.append(f"SpliceTransferData.{part}")
    for path in dest.glob("Part[0-9][0-9][0-9].lean"):
        if f"SpliceTransferData.{path.stem}" not in parts:
            path.unlink()
    checks = ", ".join(x + "_checked" for x in all_names)
    n = sum(all_sizes)
    body = [f"def groups : List Group := {lean_list(all_names)}", "",
            "theorem checked : ∀ g ∈ groups, g.Checked := by",
            "  simp only [groups, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]",
            "  exact " + (checks if len(all_names) == 1 else f"⟨{checks}⟩"), "",
            f"theorem size_sum : (groups.map Group.size).sum = {n} := by",
            "  simp only [groups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,",
            "    " + ", ".join(x + "_size" for x in all_names) + "] <;> decide"]
    write_source(directory / "SpliceTransferData.lean", parts[-2:], body)
    return n*12


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--discover", action="store_true", help="rerun reverse enumeration and regenerate the compact data")
    args = parser.parse_args()
    sources = {stem: json.loads((ROOT / f"{stem}.json").read_text())
               for stem in [*SOURCE_MODULES, "splice_further"]}
    target = ROOT / "splice_transfer.json"
    if args.discover:
        data = discover_transfer(sources)
        target.write_text(json.dumps(data, indent=2) + "\n")
    else:
        data = json.loads(target.read_text())
    count = generate_transfer(data, sources, ROOT)
    print(f"{len(data['groups'])} transfer groups certify {count:,} additional labeled boards.")

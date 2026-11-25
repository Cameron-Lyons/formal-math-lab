"""Generate the fifth or sixth splice certificate, allowing disjoint tail ranges on an existing signature."""

import argparse
import json
import subprocess
from pathlib import Path

from prepare_prefix_classifier import LAYERS, generate_classifier
from prepare_splice_extension import generate_packed_data, total
from prepare_splice_transfer import expand_transfer, signature

ROOT = Path(__file__).resolve().parent
NEXT = ("SpliceNextData", "splice_next.json")
SIXTH = ("SpliceSixthData", "splice_sixth.json")


def validate_ranges(sources, new):
    """Check that each claimed extension names its actual original cap family."""
    latest_tail = {}
    earlier_layers = {}
    for layer, data in [*sources.items(), (None, new)]:
        for i, group in enumerate(data["groups"]):
            caps, pivot, tails = group["caps"], group["pivot"], group["tails"]
            if not caps or not tails:
                raise ValueError(f"group {i} requires at least one cap and tail")
            key = signature(caps[0], pivot)
            if "extends" in group:
                parent = group["extends"]
                source, index = parent["layer"], parent["index"]
                if (
                    source not in earlier_layers
                    or type(index) is not int
                    or not 0 <= index < len(earlier_layers[source]["groups"])
                ):
                    raise ValueError(f"group {i} names an unknown earlier group")
                original = earlier_layers[source]["groups"][index]
                if (caps, pivot) != (original["caps"], original["pivot"]):
                    raise ValueError(f"group {i} does not extend its named cap family")
                if tails[0] <= latest_tail[key]:
                    raise ValueError(f"group {i} overlaps an earlier tail interval")
            elif key in latest_tail:
                raise ValueError(
                    f"group {i} repeats a signature without identifying an earlier group"
                )
            latest_tail[key] = tails[-1]
        earlier_layers[layer] = data


def write_theorem(directory, layers, count, sixth=False):
    stage = "sixth" if sixth else "next"
    layer_count = "six" if sixth else "five"
    classifier = f"Splice{stage.title()}PrefixData"
    group_list = layers[0][0] + ".groups"
    checked = layers[0][0] + ".checked"
    for module, _ in layers[1:]:
        group_list = f"({group_list} ++ {module}.groups)"
        checked = f"List.forall_mem_append.mpr ⟨{checked}, {module}.checked⟩"
    sizes = ",\n      ".join(module + ".size_sum" for module, _ in layers[1:])
    visibility = "" if sixth else "private "
    size_fact = ""
    if sixth:
        size_fact = f"""theorem sixthSize : (sixthGroups.map Group.size).sum = {count // 12} := by
  simp only [sixthGroups, List.map_append, List.sum_append, firstLayerSize,
      {sizes}] <;> decide

"""
    proof = f"""import SpliceRanges
import {classifier}

-- Generated from {layer_count} splice certificates by prepare_splice_next.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

private theorem firstLayerSize : (SpliceData.groups.map Group.size).sum = {total(layers[0][1]) // 12} := by
  decide +kernel

{visibility}def {stage}Groups : List Group :=
  {group_list}

{visibility}theorem {stage}Checked : ∀ g ∈ {stage}Groups, g.Checked :=
  {checked}

{visibility}theorem {stage}Cut : ∀ g ∈ {stage}Groups, g.k = 5 := by decide +kernel

{visibility}theorem {stage}Distinct : ({stage}Groups.flatMap Group.boards).Nodup := by
  apply groups_nodup_of_separated 5 {stage}Groups {stage}Checked {stage}Cut
  decide +kernel

{size_fact}/-- Distinct labeled boards certified by {layer_count} row-five splice layers. -/
theorem at_least_{count} :
    ∃ f : Fin {count} → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply prefix_orbit_lower_bound_of_nodup 5 {stage}Groups {classifier}.classify {count}
    {stage}Checked {stage}Cut {stage}Distinct {classifier}.classified
  simp only [{stage}Groups, List.map_append, List.sum_append, firstLayerSize,
      {sizes}] <;> decide

end TBoards

#print axioms TBoards.at_least_{count}
"""
    path = directory / f"Splice{stage.title()}Certificates.lean"
    if not path.exists() or path.read_text() != proof:
        path.write_text(proof)


def generate_next(directory, sixth=False):
    targets = [*LAYERS, NEXT, SIXTH] if sixth else [*LAYERS, NEXT]
    layers = [
        (module, json.loads((directory / filename).read_text()))
        for module, filename in targets
    ]
    sources = {
        Path(filename).stem: data
        for (_, filename), (_, data) in zip(LAYERS[:3], layers[:3], strict=False)
    }
    sources["splice_transfer"] = expand_transfer(layers[3][1], sources)
    if sixth:
        sources[Path(NEXT[1]).stem] = layers[4][1]
    new = layers[-1][1]
    validate_ranges(sources, new)
    module, witness = targets[-1]
    generate_packed_data(
        layers[0][1], new, directory, further=True, namespace=module, witness=witness
    )
    generate_classifier(layers, directory, module.removesuffix("Data") + "PrefixData")
    count = sum(total(source) for source in sources.values()) + total(new)
    write_theorem(directory, layers, count, sixth)
    return count


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--build", action="store_true", help="check the resulting theorem with Lean"
    )
    parser.add_argument(
        "--sixth", action="store_true", help="generate the six-layer combined proof"
    )
    args = parser.parse_args()
    count = generate_next(ROOT, sixth=args.sixth)
    layer_count = "six" if args.sixth else "five"
    print(
        f"Generated the {layer_count}-layer Lean certificate for {count:,} labeled boards.",
        flush=True,
    )
    if args.build:
        target = "SpliceSixthCertificates" if args.sixth else "SpliceNextCertificates"
        subprocess.run(["lake", "build", target], cwd=ROOT, check=True)

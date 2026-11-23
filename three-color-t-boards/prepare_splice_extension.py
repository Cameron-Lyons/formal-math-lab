"""Generate the packed Lean certificate for the additional row-five splice groups."""
import argparse
import json
import subprocess
from pathlib import Path

from prepare_splice import lean_list, pattern_codes, split_rows

ROOT = Path(__file__).resolve().parent
BATCH_SIZE = 512
BATCHES_PER_MODULE = 4
BUILD_JOBS = 2
BUILD_LANES = 3
# The first thirteen cap templates were certified together. Later signatures
# get separate modules so extending the data cannot invalidate those proofs.
BASE_TEMPLATE_COUNT = 13


def write_module(path, imports, body, namespace, witness):
    content = "\n".join("import " + name for name in imports)
    content += f"""

-- Generated from {witness} by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards.{namespace}
open Splice

""" + "\n".join(body) + f"\nend TBoards.{namespace}\n"
    if not path.exists() or path.read_text() != content:
        path.write_text(content)


def total(data):
    return sum(12 * len(g["caps"]) * len(g["tails"]) for g in data["groups"])


def code_list(numbers):
    return "[\n  " + ",\n  ".join(
        ", ".join(map(str, numbers[i:i+3])) for i in range(0, len(numbers), 3)
    ) + "]"


def generate_packed_data(old, extension, directory, further=False, *, namespace=None, witness=None):
    if old["cut"] != 5 or extension["cut"] != 5 or not extension["groups"]:
        raise ValueError("the packed certificate requires a row-five cut and at least one new group")
    namespace = namespace or ("SpliceFurtherData" if further else "SpliceExtensionData")
    shared_templates = 0 if further else BASE_TEMPLATE_COUNT
    witness = witness or ("splice_further.json" if further else "splice_extension.json")

    def write(path, imports, body):
        write_module(path, imports, body, namespace, witness)

    generated = directory / namespace
    generated.mkdir(parents=True, exist_ok=True)
    base_templates, assemblies, names = [], [], []
    extra_templates = set()
    modules, last_modules = [], []
    for i, group in enumerate(extension["groups"]):
        pivot, caps, tails = group["pivot"], group["caps"], group["tails"]
        split_rows(pivot, 5, 6)
        if not caps or not tails:
            raise ValueError(f"group {i} has an empty list of pieces")
        upper = pattern_codes(split_rows(caps[0], 0, 5) + [pivot])
        lower = pattern_codes([pivot] + split_rows(tails[0], 6, 10))
        if sorted(upper + lower) != list(range(81)):
            raise ValueError(f"incompatible sample pieces in group {i}")
        template = f"template{i}"
        templates = base_templates if i < shared_templates else []
        templates += [
            f"def {template} : Group where", "  k := 5",
            f"  pivot := {lean_list(pivot)}", "  caps := []", "  tails := []",
            f"  upperMask := {sum(1 << c for c in upper)}",
            f"  lowerMask := {sum(1 << c for c in lower)}", "",
        ]
        tails_in_group = []
        pieces = []
        for side, flats, start, stop in [("cap", caps, 0, 5), ("tail", tails, 6, 10)]:
            if flats != sorted(set(flats)):
                raise ValueError(f"{side} pieces in group {i} must be sorted and distinct")
            piece_batches = []
            for offset in range(0, len(flats), BATCH_SIZE):
                chunk = flats[offset:offset+BATCH_SIZE]
                for flat in chunk:
                    split_rows(flat, start, stop)
                name = f"{side}{i}_{len(piece_batches)}"
                codes = code_list([int(flat, 3) for flat in chunk])
                declaration = [
                    f"private def {name}Codes : List Nat := {codes}", "",
                    f"def {name} : Group.Batch {template}.{side}OK :=",
                    f"  Packed.{side}Batch {template} {int(pivot, 3)} rfl (by decide) {name}Codes",
                    "    (by decide +kernel)", "",
                ]
                # Caps are small, and all tail workers can import their definitions.
                if side == "cap":
                    templates.extend(declaration)
                else:
                    tails_in_group.append(declaration)
                piece_batches.append(name)
            pieces.append(lean_list(piece_batches))
        extra_template = None
        if i >= shared_templates:
            extra_template = f"{namespace}.Template{i:03}"
            extra_templates.add(extra_template)
            write(generated / f"Template{i:03}.lean", ["SplicePacked"], templates)
        # Each lane is serial even when Lake schedules every target at once.
        previous = last_modules[i-BUILD_LANES] if i >= BUILD_LANES else f"{namespace}.Groups"
        for part, start in enumerate(range(0, len(tails_in_group), BATCHES_PER_MODULE)):
            module = f"Group{i:03}Part{part:03}"
            body = [line for batch in tails_in_group[start:start+BATCHES_PER_MODULE] for line in batch]
            imports = [previous]
            if part == 0 and extra_template:
                imports.append(extra_template)
            write(generated / (module + ".lean"), imports, body)
            previous = namespace + "." + module
            modules.append(previous)
        last_modules.append(previous)
        name = f"group{i}"
        names.append(name)
        assemblies += [
            f"def {name} := Group.assemble {template} {pieces[0]} {pieces[1]}",
            f"theorem {name}_checked : {name}.Checked := by",
            "  apply Group.assemble_checked <;> decide +kernel",
            f"private theorem {name}_size : {name}.size = {len(caps) * len(tails)} := by decide +kernel", "",
        ]

    write(generated / "Groups.lean", ["SplicePacked"], base_templates)
    for path in generated.glob("Template[0-9][0-9][0-9].lean"):
        if namespace + "." + path.stem not in extra_templates:
            path.unlink()
    for path in generated.glob("Group[0-9][0-9][0-9]Part[0-9][0-9][0-9].lean"):
        if namespace + "." + path.stem not in modules:
            path.unlink()

    checked = ", ".join(name + "_checked" for name in names)
    if len(names) > 1:
        checked = "⟨" + checked + "⟩"
    assemblies += [
        f"def groups : List Group := {lean_list(names)}", "",
        "theorem checked : ∀ g ∈ groups, g.Checked := by",
        "  simp only [groups, List.forall_mem_cons, List.not_mem_nil, false_implies,",
        "    implies_true, and_true]", f"  exact {checked}", "",
        f"theorem size_sum : (groups.map Group.size).sum = {total(extension) // 12} := by",
        "  simp only [groups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,",
        "    " + ", ".join(name + "_size" for name in names) + "] <;> decide", "",
    ]
    if not further:
        markers = []
        for group in old["groups"] + extension["groups"]:
            for cap in group["caps"]:
                marker = cap[0] + group["pivot"] + cap[0]
                if marker not in markers:
                    markers.append(marker)
        assemblies += [
            "def markers : List (List Nat) := [",
            "  " + ",\n  ".join(lean_list(marker) for marker in markers) + "]",
        ]
    write(directory / (namespace + ".lean"), last_modules[-BUILD_LANES:], assemblies)


def generate(old, extension, directory):
    """Regenerate the original two-layer proof and its packed extension data."""
    generate_packed_data(old, extension, directory)
    count = total(old) + total(extension)
    proof = f"""import SpliceData
import SpliceExtensionData
import SpliceSymmetry

-- Generated from the two splice certificates by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

/-- At least {count:,} distinct labeled T boards arise from the two splice certificates. -/
theorem at_least_{count} :
    ∃ f : Fin {count} → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply orbit_lower_bound 5 (SpliceData.groups ++ SpliceExtensionData.groups)
    SpliceExtensionData.markers {count}
  · exact List.forall_mem_append.mpr ⟨SpliceData.checked, SpliceExtensionData.checked⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [List.map_append, List.sum_append, SpliceExtensionData.size_sum]
    decide +kernel

end TBoards

#print axioms TBoards.at_least_{count}
"""
    path = directory / "SpliceExtensionCertificates.lean"
    if not path.exists() or path.read_text() != proof:
        path.write_text(proof)
    return count


def write_further_theorem(directory, base_count, count):
    """Join four disjoint, kernel-checked layers using their certified prefix classifier."""
    proof = f"""import SplicePrefixData

-- Generated from the four splice certificates by prepare_splice_extension.py.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards
open Splice

private theorem firstLayerSize : (SpliceData.groups.map Group.size).sum = {base_count // 12} := by
  decide +kernel

/-- At least {count:,} distinct valid labeled T boards arise from the four splice certificates. -/
theorem at_least_{count} :
    ∃ f : Fin {count} → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  apply prefix_orbit_lower_bound 5
    (((SpliceData.groups ++ SpliceExtensionData.groups) ++ SpliceFurtherData.groups) ++
      SpliceTransferData.groups) SplicePrefixData.classify {count}
  · exact List.forall_mem_append.mpr
      ⟨List.forall_mem_append.mpr
        ⟨List.forall_mem_append.mpr ⟨SpliceData.checked, SpliceExtensionData.checked⟩,
          SpliceFurtherData.checked⟩, SpliceTransferData.checked⟩
  · decide +kernel
  · decide +kernel
  · exact SplicePrefixData.classified
  · simp only [List.map_append, List.sum_append, firstLayerSize, SpliceExtensionData.size_sum,
      SpliceFurtherData.size_sum, SpliceTransferData.size_sum] <;> decide

end TBoards

#print axioms TBoards.at_least_{count}
"""
    path = directory / "SpliceFurtherCertificates.lean"
    if not path.exists() or path.read_text() != proof:
        path.write_text(proof)


def generate_further(directory):
    """Regenerate new explicit groups, transfers, classifier and the combined proof."""
    from prepare_prefix_classifier import LAYERS, generate_classifier
    from prepare_splice_transfer import generate_transfer
    from verify_splice import combine

    layers = [(module, json.loads((directory / filename).read_text())) for module, filename in LAYERS]
    base, extension, further, transfer = [data for _, data in layers]
    sources = {Path(filename).stem: data for (_, filename), (_, data) in zip(LAYERS[:3], layers[:3])}
    generate_packed_data(combine(base, extension), further, directory, further=True)
    transfer_count = generate_transfer(transfer, sources, directory)
    generate_classifier(layers, directory)
    count = total(base) + total(extension) + total(further) + transfer_count
    write_further_theorem(directory, total(base), count)
    return count


def build(directory, groups, further=False):
    namespace = "SpliceFurtherData" if further else "SpliceExtensionData"
    # Select two group targets at a time when less memory or CPU is available.
    targets = [sorted((directory / namespace).glob(f"Group{i:03}Part*.lean"))[-1]
               for i in range(len(groups))]
    for i in range(0, len(targets), BUILD_JOBS):
        modules = ["+" + namespace + "." + path.stem for path in targets[i:i+BUILD_JOBS]]
        subprocess.run(["lake", "build", *modules], cwd=directory, check=True)
    subprocess.run(["lake", "build", namespace.replace("Data", "Certificates")], cwd=directory, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="build two groups at a time and check the final theorem")
    parser.add_argument("--further", action="store_true", help="generate the four-layer combined proof")
    args = parser.parse_args()
    if args.further:
        result = generate_further(ROOT)
        packed_witness = "splice_further.json"
    else:
        base = json.loads((ROOT / "splice_witnesses.json").read_text())
        packed_witness = "splice_extension.json"
        extension = json.loads((ROOT / packed_witness).read_text())
        result = generate(base, extension, ROOT)
    print(f"Generated the combined Lean certificate for {result:,} boards.", flush=True)
    if args.build:
        groups = json.loads((ROOT / packed_witness).read_text())["groups"]
        build(ROOT, groups, args.further)

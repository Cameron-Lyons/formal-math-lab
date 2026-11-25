"""Package source, certificates, and audit logs; exclude local build products."""

import hashlib
import json
import zipfile
from pathlib import Path

from verify_splice import load_all, verify

ROOT = Path(__file__).resolve().parent


def main():
    files = [
        "README.md",
        "PROOF.md",
        "PRIOR_ART.md",
        "simple_proof.py",
        "SimpleProof.lean",
        "TBoards.lean",
        "BoardData.lean",
        "Certificates.lean",
        "EfficientCheck.lean",
        "ColorSymmetry.lean",
        "SortedFamily.lean",
        "CertifiedFamily.lean",
        "Extended.lean",
        "ExtendedCertificates.lean",
        "lean-toolchain",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-build.log",
        "simple-lean-build.log",
        "extended-lean-build.log",
        "prefix_result.json",
        "family.json",
        "novel_patterns.csv",
        "extended_seeds.json",
        "extended_family.json",
        "extended_summary.json",
        "extended_prefix0.jsonl",
        "extended_prefix0_summary.json",
        "more_results.jsonl",
        "more_search.log",
        "prepare_certificates.py",
        "prepare_extended.py",
        "collect_extended.py",
        "verify_certificate.py",
        "more_audit.py",
        "reproduce_search.py",
        "reproduce_extended_search.py",
        "search_prefix.cpp",
        "extended_search.cpp",
        "more_search.cpp",
        "package_proof.py",
        "SPLICE_PROOF.md",
        "Splice.lean",
        "SpliceSymmetry.lean",
        "SpliceData.lean",
        "SpliceCertificates.lean",
        "splice_witnesses.json",
        "verify_splice.py",
        "prepare_splice.py",
        "reproduce_splice.py",
        "splice_search.cpp",
        "splice-lean-build.log",
        "BINARY_CAPS.md",
        "SplicePacked.lean",
        "SpliceExtensionData.lean",
        "SpliceExtensionCertificates.lean",
        "splice_extension.json",
        "prepare_splice_extension.py",
        "splice-extension-lean-build.log",
        "SPLICE_FURTHER.md",
        "splice_further.json",
        "splice_transfer.json",
        "SpliceFurtherData.lean",
        "SpliceFurtherCertificates.lean",
        "SplicePrefixSymmetry.lean",
        "SplicePrefixData.lean",
        "prepare_prefix_classifier.py",
        "SpliceTransfer.lean",
        "SpliceTransferData.lean",
        "prepare_splice_transfer.py",
        "search_splice_transfer.cpp",
        "splice-further-lean-build.log",
        "splice-further-audit.log",
        "reproduce_symmetric.py",
        "SPLICE_RANGES.md",
        "splice_next.json",
        "SpliceRanges.lean",
        "SpliceNextData.lean",
        "SpliceNextPrefixData.lean",
        "SpliceNextCertificates.lean",
        "prepare_splice_next.py",
        "find_rare_caps.py",
        "splice-next-lean-build.log",
        "splice-next-audit.log",
        "SPLICE_PALINDROMES.md",
        "splice_sixth.json",
        "splice_pal.json",
        "SpliceSixthData.lean",
        "SpliceSixthPrefixData.lean",
        "SpliceSixthCertificates.lean",
        "SplicePal.lean",
        "SplicePalData.lean",
        "SplicePalCertificates.lean",
        "prepare_splice_pal.py",
        "find_palindromic_caps.py",
        "splice-pal-build.log",
        "splice-pal-audit.log",
        "splice-pal-census.log",
        "expand_splice.cpp",
        "EXACT_COUNT.md",
        "ExactSymmetry.lean",
        "exact-symmetry-lean-build.log",
        "ExactOrbit.lean",
        "exact-orbit-lean-build.log",
    ]
    # Keep the README's exact-count companion and its small source and evidence files together.
    experiments = ROOT / "experiments"
    files += [
        str(p.relative_to(ROOT))
        for p in sorted(experiments.glob("exact_*"))
        if p.is_file()
        and p.suffix in {".cpp", ".hpp", ".py", ".md", ".json", ".log", ".txt"}
    ]
    files += [
        str(p.relative_to(ROOT)) for p in sorted((ROOT / "Extended").glob("*.lean"))
    ]
    files += [
        str(p.relative_to(ROOT)) for p in sorted((ROOT / "SpliceData").glob("*.lean"))
    ]
    files += [
        str(p.relative_to(ROOT))
        for p in sorted((ROOT / "SpliceExtensionData").glob("*.lean"))
    ]
    for layer in (
        "SpliceFurtherData",
        "SpliceTransferData",
        "SpliceNextData",
        "SpliceSixthData",
        "SplicePalData",
    ):
        files += [
            str(p.relative_to(ROOT)) for p in sorted((ROOT / layer).glob("*.lean"))
        ]
    files += [
        str(p.relative_to(ROOT))
        for p in sorted((ROOT / "sources").rglob("*"))
        if p.is_file() and "__pycache__" not in p.parts
    ]
    bound = verify(load_all())[-1]
    output = ROOT / f"tboards-{bound}-proof.zip"
    hashes = {}
    with zipfile.ZipFile(output, "w", zipfile.ZIP_DEFLATED) as z:
        for name in files:
            contents = (ROOT / name).read_bytes()
            hashes[name] = hashlib.sha256(contents).hexdigest()
            z.writestr(name, contents)
        z.writestr("PROOF_SHA256SUMS.json", json.dumps(hashes, indent=2) + "\n")
    with zipfile.ZipFile(output) as z:
        if z.testzip() is not None:
            raise ValueError("Archive checksum failure")
        for name, expected in hashes.items():
            if hashlib.sha256(z.read(name)).hexdigest() != expected:
                raise ValueError(f"Archive source mismatch: {name}")
    print(f"{output.name}: {output.stat().st_size} bytes; {len(files)} files checked.")


if __name__ == "__main__":
    main()

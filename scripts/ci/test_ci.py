"""Unit tests for repository CI scripts."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.ci.check_c_cpp import (
    EXTERNAL_DEP_FILES,
    classify_sources,
)
from scripts.ci.check_repo import (
    check_lean_reachability,
    check_markdown_links,
    scan_lean_source,
    strip_lean_comments_and_strings,
)
from scripts.ci.packages import (
    CANARY_PACKAGE,
    EXTENDED_TIMEOUT_PACKAGES,
    EXTRA_LEAN_CHECK_FILES,
    HEAVY_PACKAGES,
    REPO_ROOT,
    SEQUENTIAL_PREBUILD_TARGETS,
    THIRD_PARTY_WARNING_PACKAGES,
    affected_packages,
    build_matrix,
    discover_packages,
)


class LeanScannerTests(unittest.TestCase):
    def test_ignores_comments_and_strings(self) -> None:
        source = """
-- sorry admit axiom fake
/-
  nested /- sorry -/
  admit
  axiom inside_block : False
-/
def msg : String := "sorry admit axiom fake \\"quoted\\""
theorem ok : True := trivial
"""
        errors, seen = scan_lean_source("Demo/Ok.lean", source)
        self.assertEqual(errors, [])
        self.assertEqual(seen, set())

    def test_catches_sorry_admit_and_unallowlisted_axiom(self) -> None:
        source = """
theorem bad1 : True := by sorry
theorem bad2 : True := by admit
axiom sneaky : False
unsafe def escape : Nat := 0
@[implemented_by escape] def wrapper : Nat := 0
"""
        errors, _ = scan_lean_source("Demo/Bad.lean", source)
        self.assertEqual(len(errors), 5)
        self.assertIn("sorry", errors[0])
        self.assertIn("admit", errors[1])
        self.assertIn("sneaky", errors[2])
        self.assertIn("unsafe", errors[3])
        self.assertIn("implemented_by", errors[4])

    def test_allows_only_allowlisted_axiom(self) -> None:
        source = "axiom formulas_48_24_unsat : True\n"
        errors, seen = scan_lean_source(
            "combinatorics/queen-domination-48/sat/Certified48.lean", source
        )
        self.assertEqual(errors, [])
        self.assertEqual(
            seen,
            {
                (
                    "combinatorics/queen-domination-48/sat/Certified48.lean",
                    "formulas_48_24_unsat",
                )
            },
        )

    def test_preserves_line_numbers(self) -> None:
        source = "/-\nline 2\nline 3\n-/\ntheorem bad : True := by\n  sorry\n"
        stripped = strip_lean_comments_and_strings(source)
        self.assertEqual(len(stripped.splitlines()), len(source.splitlines()))
        errors, _ = scan_lean_source("Demo/Lines.lean", source)
        self.assertEqual(len(errors), 1)
        self.assertTrue(errors[0].startswith("Demo/Lines.lean:6:"))


class StaticLinkAndReachabilityTests(unittest.TestCase):
    def test_detects_broken_relative_markdown_link(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "ok.txt").write_text("hi\n", encoding="utf-8")
            (root / "README.md").write_text(
                "[good](ok.txt) [ext](https://example.com) [bad](missing.md#sec)\n",
                encoding="utf-8",
            )
            errors = check_markdown_links(root, ["README.md"])
            self.assertEqual(len(errors), 1)
            self.assertIn("missing.md#sec", errors[0])

    def test_detects_unreachable_lean_module(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pkg = root / "demo"
            pkg.mkdir()
            (pkg / "lean-toolchain").write_text(
                "leanprover/lean4:v4.36.0\n", encoding="utf-8"
            )
            (pkg / "lakefile.toml").write_text(
                'name = "demo"\ndefaultTargets = ["Main"]\n\n'
                '[[lean_lib]]\nname = "Main"\n',
                encoding="utf-8",
            )
            (pkg / "Main.lean").write_text("import Helper\n", encoding="utf-8")
            (pkg / "Helper.lean").write_text("def x := 1\n", encoding="utf-8")
            (pkg / "Orphan.lean").write_text("def y := 2\n", encoding="utf-8")
            packages = discover_packages(root, tracked_only=False)
            errors = check_lean_reachability(
                root,
                packages,
                ["demo/Main.lean", "demo/Helper.lean", "demo/Orphan.lean"],
            )
            self.assertEqual(len(errors), 1)
            self.assertIn("demo/Orphan.lean", errors[0])


class PackageDiscoveryTests(unittest.TestCase):
    def test_discovers_all_repo_packages(self) -> None:
        packages = discover_packages(REPO_ROOT)
        self.assertGreaterEqual(len(packages), 40)
        self.assertIn("number-theory/unit-fractions/even", packages)
        self.assertIn("combinatorics/queen-domination-48/sat", packages)
        self.assertIn("combinatorics/queen-domination-48/sat/lean-sat", packages)
        self.assertIn("combinatorics/queen-domination-48/sat/lean-check", packages)
        self.assertNotIn("lake-compat", packages)
        self.assertTrue(packages["oeis/a026019-binomial-recurrence"].uses_mathlib_cache)
        self.assertFalse(
            packages["number-theory/unit-fractions/even"].uses_mathlib_cache
        )
        for heavy in HEAVY_PACKAGES:
            self.assertTrue(packages[heavy].heavy)
        for pkg_name in THIRD_PARTY_WARNING_PACKAGES:
            self.assertIn(pkg_name, packages)
            self.assertTrue(packages[pkg_name].warning_as_error)
        for pkg_name in EXTENDED_TIMEOUT_PACKAGES:
            self.assertIn(pkg_name, packages)
            self.assertFalse(packages[pkg_name].heavy)
        for pkg_name, targets in SEQUENTIAL_PREBUILD_TARGETS.items():
            self.assertIn(pkg_name, packages)
            self.assertEqual(packages[pkg_name].prebuild_targets, targets)
            for target in targets:
                mod_file = REPO_ROOT / pkg_name / f"{target.replace('.', '/')}.lean"
                self.assertTrue(mod_file.is_file(), f"Missing {mod_file}")
        for pkg_name, extra_files in EXTRA_LEAN_CHECK_FILES.items():
            self.assertIn(pkg_name, packages)
            self.assertEqual(packages[pkg_name].extra_check_files, extra_files)
            for extra in extra_files:
                self.assertTrue((REPO_ROOT / pkg_name / extra).is_file())

    def test_reverse_dependencies_propagate(self) -> None:
        packages = discover_packages(REPO_ROOT)
        self.assertEqual(
            affected_packages(packages, ["etp/e670-order-10/E670/Basic.lean"]),
            ["etp/e670-order-10", "etp/e677-e255-order-9"],
        )
        self.assertEqual(
            affected_packages(
                packages,
                [
                    "combinatorics/queen-domination-48/sat/lean-sat/QueenDomSat.lean",
                ],
            ),
            [
                "combinatorics/queen-domination-48/sat",
                "combinatorics/queen-domination-48/sat/lean-check",
                "combinatorics/queen-domination-48/sat/lean-sat",
            ],
        )

    def test_non_lean_files_do_not_trigger_lean_builds(self) -> None:
        packages = discover_packages(REPO_ROOT)
        self.assertEqual(
            affected_packages(
                packages,
                [
                    "combinatorics/queen-domination-48/sat/README.md",
                    "erdos/272-ap-intersections/thirteen/clique_search/verify.cpp",
                    "erdos/677-equal-lcms/search/height.py",
                    "erdos/677-equal-lcms/cubic/ellipticGroups.gp",
                    "erdos/272-ap-intersections/sixteen/rank.weights",
                    "etp/e1486-order-15/LICENSE",
                    "combinatorics/three-color-t-boards/sources/LICENSE_SCOPE.txt",
                    "combinatorics/three-stacks/evidence/results.tar.gz",
                    "combinatorics/three-stacks/evidence/SHA256SUMS",
                ],
            ),
            [],
        )
        self.assertEqual(
            affected_packages(
                packages,
                [
                    "erdos/835-coloring-subsets/certificates/order17-19.json",
                    "combinatorics/ramsey-3-10/certificates/two-orbits.lrat",
                    "erdos/160-four-term-ap/progression_families.txt",
                ],
            ),
            [
                "combinatorics/ramsey-3-10",
                "erdos/160-four-term-ap",
                "erdos/835-coloring-subsets",
            ],
        )

    def test_ci_change_triggers_canary_only(self) -> None:
        packages = discover_packages(REPO_ROOT)
        self.assertEqual(
            affected_packages(packages, [".github/workflows/ci.yml"]),
            [CANARY_PACKAGE],
        )
        self.assertEqual(
            affected_packages(packages, ["scripts/ci/install_elan.sh"]),
            [CANARY_PACKAGE],
        )
        self.assertEqual(affected_packages(packages, ["README.md"]), [])

    def test_matrix_timeouts(self) -> None:
        packages = discover_packages(REPO_ROOT)
        matrix = build_matrix(
            packages,
            [
                "number-theory/unit-fractions/even",
                "erdos/556-cycle-ramsey",
                "etp/e670-order-10",
            ],
        )
        self.assertEqual(matrix[0]["timeout_minutes"], 45)
        self.assertEqual(matrix[1]["timeout_minutes"], 90)
        self.assertEqual(matrix[2]["timeout_minutes"], 180)


class CCppClassificationTests(unittest.TestCase):
    def test_classifies_new_files_automatically(self) -> None:
        tracked = [
            *sorted(EXTERNAL_DEP_FILES),
            "demo/new_tool.c",
            "demo/new_search.cpp",
        ]
        result = classify_sources(tracked)
        self.assertEqual(result.stale_exclusions, ())
        self.assertEqual(result.c_files, ("demo/new_tool.c",))
        self.assertEqual(result.cpp_files, ("demo/new_search.cpp",))
        self.assertEqual(len(result.skipped_external_deps), len(EXTERNAL_DEP_FILES))


if __name__ == "__main__":
    unittest.main()

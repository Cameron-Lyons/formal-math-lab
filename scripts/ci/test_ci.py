"""Unit tests for repository CI scripts."""

from __future__ import annotations

import unittest

from scripts.ci.check_c_cpp import (
    EXTERNAL_DEP_FILES,
    THIRD_PARTY_FILES,
    classify_sources,
)
from scripts.ci.check_repo import scan_lean_source, strip_lean_comments_and_strings
from scripts.ci.packages import (
    CANARY_PACKAGE,
    EXTENDED_TIMEOUT_PACKAGES,
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
            "queen-domination-48-sat/Certified48.lean", source
        )
        self.assertEqual(errors, [])
        self.assertEqual(
            seen,
            {("queen-domination-48-sat/Certified48.lean", "formulas_48_24_unsat")},
        )

    def test_preserves_line_numbers(self) -> None:
        source = "/-\nline 2\nline 3\n-/\ntheorem bad : True := by\n  sorry\n"
        stripped = strip_lean_comments_and_strings(source)
        self.assertEqual(len(stripped.splitlines()), len(source.splitlines()))
        errors, _ = scan_lean_source("Demo/Lines.lean", source)
        self.assertEqual(len(errors), 1)
        self.assertTrue(errors[0].startswith("Demo/Lines.lean:6:"))


class PackageDiscoveryTests(unittest.TestCase):
    def test_discovers_all_repo_packages(self) -> None:
        packages = discover_packages(REPO_ROOT)
        self.assertGreaterEqual(len(packages), 40)
        self.assertIn("26-unit-fractions", packages)
        self.assertIn("queen-domination-48-sat", packages)
        self.assertIn("queen-domination-48-sat/lean-sat", packages)
        self.assertIn("queen-domination-48-sat/lean-check", packages)
        self.assertNotIn("lake-compat", packages)
        self.assertTrue(packages["a026019-binomial-recurrence"].uses_mathlib_cache)
        self.assertFalse(packages["26-unit-fractions"].uses_mathlib_cache)
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

    def test_reverse_dependencies_propagate(self) -> None:
        packages = discover_packages(REPO_ROOT)
        self.assertEqual(
            affected_packages(packages, ["E670-order-10/E670/Basic.lean"]),
            ["E670-order-10", "E677-E255-order-9"],
        )
        self.assertEqual(
            affected_packages(
                packages, ["queen-domination-48-sat/lean-sat/QueenDomSat.lean"]
            ),
            [
                "queen-domination-48-sat",
                "queen-domination-48-sat/lean-check",
                "queen-domination-48-sat/lean-sat",
            ],
        )

    def test_non_lean_files_do_not_trigger_lean_builds(self) -> None:
        packages = discover_packages(REPO_ROOT)
        self.assertEqual(
            affected_packages(
                packages,
                [
                    "queen-domination-48-sat/README.md",
                    "erdos-272-thirteen/clique_search/verify.cpp",
                    "three-stacks/verify/build_witnesses.py",
                    "E1486-order-15/LICENSE",
                ],
            ),
            [],
        )
        self.assertEqual(
            affected_packages(
                packages,
                [
                    "erdos-835-coloring-subsets/certificates/order17-19.json",
                    "ramsey-3-10/certificates/two-orbits.lrat",
                ],
            ),
            ["erdos-835-coloring-subsets", "ramsey-3-10"],
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
            ["26-unit-fractions", "erdos-556-cycle-ramsey", "E670-order-10"],
        )
        self.assertEqual(matrix[0]["timeout_minutes"], 45)
        self.assertEqual(matrix[1]["timeout_minutes"], 90)
        self.assertEqual(matrix[2]["timeout_minutes"], 180)


class CCppClassificationTests(unittest.TestCase):
    def test_classifies_new_files_automatically(self) -> None:
        tracked = [
            *sorted(THIRD_PARTY_FILES),
            *sorted(EXTERNAL_DEP_FILES),
            "demo/new_tool.c",
            "demo/new_search.cpp",
            "three-color-t-boards/experiments/exact_parity_sources/foo.cpp",
        ]
        result = classify_sources(tracked)
        self.assertEqual(result.stale_exclusions, ())
        self.assertEqual(result.c_files, ("demo/new_tool.c",))
        self.assertEqual(result.cpp_files, ("demo/new_search.cpp",))
        self.assertEqual(len(result.skipped_external_deps), len(EXTERNAL_DEP_FILES))


if __name__ == "__main__":
    unittest.main()

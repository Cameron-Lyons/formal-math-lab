"""Independent exact-arithmetic checks for the coefficient and slope sieves."""

import unittest
from fractions import Fraction
from math import comb, lcm, prod

from height import (
    candidates,
    coefficient_ratios,
    coefficient_tables,
    multiplier_part,
    ratios,
    residue_conditions,
    start_progressions,
)


class HeightSearchTests(unittest.TestCase):
    def test_lcm_multipliers(self):
        for k in range(1, 25):
            tables = coefficient_tables(k)
            for n in [*range(120), 10**25 + k]:
                expected_lcm = lcm(*range(n + 1, n + k + 1))
                divisor = k * comb(n + k, k)
                self.assertEqual(
                    divisor * multiplier_part(n, tables), expected_lcm, (k, n)
                )

    def test_ratio_coverage(self):
        for k in range(1, 17):
            self.assertEqual(coefficient_ratios(coefficient_tables(k)), ratios(k), k)

    def test_multiplier_ratio_congruences(self):
        for k in range(1, 29):
            tables = coefficient_tables(k)
            conditions = residue_conditions(tables)
            for n in range(100):
                m = 10**35 + n * n
                ratio = Fraction(multiplier_part(n, tables), multiplier_part(m, tables))
                (a, n_step), (b, m_step) = start_progressions(ratio, conditions)
                self.assertEqual((n % n_step, m % m_step), (a, b))

    def test_restricted_progressions(self):
        for k in range(1, 25):
            for n, m in [(3, 111), (40, 71), (1201, 2017), (5711, 5780)]:
                ratio = Fraction(
                    prod(range(m + 1, m + k + 1)), prod(range(n + 1, n + k + 1))
                )
                x, y = 2 * n + k + 1, 2 * m + k + 1
                steps = ((n % 35, 35), (m % 13, 13))
                self.assertIn(
                    (x, y), candidates(k, ratio, x, True, True, steps), (k, n, m)
                )

    def test_disjoint_product_matches_survive_at_endpoint(self):
        for k in range(1, 25):
            for n in [1, 17, 99, 1000, 10**20, 10**45]:
                m = n + k + 13
                ratio = Fraction(
                    prod(range(m + 1, m + k + 1)), prod(range(n + 1, n + k + 1))
                )
                x, y = 2 * n + k + 1, 2 * m + k + 1
                self.assertIn((x, y), candidates(k, ratio, x, True, True), (k, n))


if __name__ == "__main__":
    unittest.main()

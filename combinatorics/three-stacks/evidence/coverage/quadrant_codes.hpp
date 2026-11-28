// Constant-size dual-address lookup from the two factorial codes of a prefix.
// All card labels are zero-based. Prefix positions in the dual run from the
// original deck's largest card down through its K largest cards.
#pragma once

#include "quadrant.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <vector>

namespace quadrant_codes {
struct Prefix {
  std::uint32_t high, low;
};

template <int K> constexpr std::array<unsigned, K + 1> factorials() {
  std::array<unsigned, K + 1> f{};
  f[0] = 1;
  for (int i = 1; i <= K; ++i)
    f[i] = i * f[i - 1];
  return f;
}
template <int K, class T> Prefix encode_prefix(const T *word) {
  constexpr auto f = factorials<K>();
  Prefix code{};
  unsigned seen = 0;
  for (int i = 0; i < K; ++i) {
    unsigned v = word[i], bit = 1u << v;
    unsigned smaller = std::popcount(seen & (bit - 1));
    code.low += smaller * f[v];
    code.high += (i - smaller) * f[K - 1 - v];
    seen |= bit;
  }
  return code;
}

// If d labels are retained at the bottom, the remaining high-order code uses
// only factorials below (K-d)!. The symmetric statement holds for the low
// order. The constant divisor permits reduction by a reciprocal multiply.
struct Modulus {
  unsigned divisor = 1;
  std::uint64_t reciprocal = 0;
  explicit Modulus(unsigned m = 1) : divisor(m), reciprocal((1ULL << 32) / m) {}
  unsigned of(unsigned x) const {
    unsigned q = (x * reciprocal) >> 32;
    unsigned r = x - q * divisor;
    return r >= divisor ? r - divisor : r;
  }
};

// Return the reversed-position bit mask of labels smaller than d. The
// byte-lane subtraction cannot borrow across lanes: before subtraction each
// lane is at least 128 and d is at most 8. Multiplication gathers one bit
// per byte. The scalar path also covers big-endian machines.
template <int K, class T> unsigned low_positions(const T *word, unsigned d) {
  if constexpr (sizeof(T) == 1 && K >= 8 && K <= 16 &&
                std::endian::native == std::endian::little) {
    constexpr std::uint64_t tops = 0x8080808080808080ULL;
    constexpr std::uint64_t ones = 0x0101010101010101ULL;
    constexpr std::uint64_t reverse_gather = 0x8040201008040201ULL;
    auto gather = [&](std::uint64_t v) {
      auto marked = (~((v | tops) - d * ones) & tops) >> 7;
      return unsigned((marked * reverse_gather) >> 56);
    };
    std::uint64_t a = 0, b = 0;
    std::memcpy(&a, word, 8);
    if constexpr (K > 8)
      std::memcpy(&b, word + 8, K - 8);
    return (gather(a) << (K - 8)) | (gather(b) >> (16 - K));
  } else {
    unsigned mask = 0;
    for (int i = 0; i < K; ++i)
      mask = 2 * mask + (unsigned(word[i]) < d);
    return mask;
  }
}
namespace detail {
// Blocks of three base-16 digits (one inversion count per digit). For each
// subset of the three target slots, only 16^popcount(subset) entries exist.
template <int L> struct Weighted {
  static constexpr int groups = (L + 2) / 3;
  std::array<std::array<std::vector<unsigned>, 8>, groups> lut;
  explicit Weighted(const std::array<unsigned, L> &weights) {
    for (int g = 0; g < groups; ++g)
      for (int m = 0; m < 8; ++m) {
        auto &tab = lut[g][m];
        tab.resize(1u << (4 * std::popcount(unsigned(m))));
        for (unsigned digits = 0; digits < tab.size(); ++digits) {
          unsigned x = digits, v = 0;
          for (int p = 0; p < 3; ++p)
            if (m & (1 << p)) {
              if (3 * g + p < L)
                v += (x & 15) * weights[3 * g + p];
              x >>= 4;
            }
          tab[digits] = v;
        }
      }
  }
  struct Plan {
    std::array<const unsigned *, groups> values{};
    std::array<unsigned char, groups> shift{};
    std::array<unsigned short, groups> mask{};
    unsigned operator()(std::uint64_t digits) const {
      unsigned sum = 0;
      for (int i = 0; i < groups; ++i)
        sum += values[i][(digits >> shift[i]) & mask[i]];
      return sum;
    }
  };
  Plan plan(unsigned roles) const {
    Plan p;
    unsigned shift = 0;
    for (int g = 0; g < groups; ++g) {
      auto m = (roles >> (3 * g)) & 7;
      auto width = 4 * std::popcount(m);
      p.values[g] = lut[g][m].data();
      p.shift[g] = shift;
      p.mask[g] = (1u << width) - 1;
      shift += width;
    }
    return p;
  }
};
} // namespace detail

template <int N, int K> class Tables {
  static constexpr int M = N - K - 1;
  static_assert(K >= 2 && K <= 12 && M >= 1 && M <= 8);
  static constexpr int max_high = (K < 10 ? K : 10);
  static constexpr int max_size = (max_high > M ? max_high : M);
  static constexpr auto f = factorials<K>();
  static_assert(M <= K);
  detail::Weighted<K> high_weights;
  detail::Weighted<M> low_weights;

  static std::array<unsigned, K> high_coefficients() {
    std::array<unsigned, K> x{};
    for (int i = 0; i < K; ++i)
      x[i] = f[i];
    return x;
  }
  static std::array<unsigned, M> low_coefficients() {
    std::array<unsigned, M> x{};
    for (int i = 0; i < M; ++i)
      x[i] = f[M] / f[M - i];
    return x;
  }
  static constexpr int direct_limit = 7;
  std::array<std::vector<std::uint64_t>, max_high + 1> packed_high;
  std::array<std::vector<unsigned>, 1 << K> direct_high;
  std::array<std::vector<unsigned>, 1 << M> direct_low;

public:
  Tables()
      : high_weights(high_coefficients()), low_weights(low_coefficients()) {
    std::array<std::vector<std::uint64_t>, M + 1> packed_low;
    for (int size = 0; size <= max_size; ++size) {
      if (size <= max_high)
        packed_high[size].resize(f[size]);
      if (size <= M)
        packed_low[size].resize(f[size]);
      std::array<int, max_size> p{};
      for (int i = 0; i < size; ++i)
        p[i] = i;
      do {
        unsigned seen = 0, hi = 0, lo = 0;
        std::uint64_t hd = 0, ld = 0;
        for (int pos = 0; pos < size; ++pos) {
          unsigned v = p[pos], bit = 1u << v;
          unsigned before_low = std::popcount(seen & (bit - 1));
          unsigned before_high = pos - before_low;
          hi += before_high * f[size - 1 - v];
          lo += before_low * f[v];
          hd |= std::uint64_t(v - before_low) << (4 * v);
          ld |= std::uint64_t(before_high) << (4 * v);
          seen |= bit;
        }
        if (size <= max_high)
          packed_high[size][hi] = hd;
        if (size <= M)
          packed_low[size][lo] = ld;
      } while (std::next_permutation(p.begin(), p.begin() + size));
    }
    for (unsigned m = 0; m < direct_low.size(); ++m) {
      unsigned size = std::popcount(m);
      auto plan = low_weights.plan(m);
      auto &out = direct_low[m];
      out.reserve(f[size]);
      for (auto bits : packed_low[size])
        out.push_back(plan(bits));
    }
    for (unsigned m = 0; m < direct_high.size(); ++m) {
      int size = std::popcount(m);
      if (size < K - M || size > direct_limit)
        continue;
      auto plan = high_weights.plan(m);
      auto &out = direct_high[m];
      out.reserve(f[size]);
      for (auto bits : packed_high[size])
        out.push_back(plan(bits));
    }
  }

  struct Block {
    using Baseline = quadrant::Encoder<N, K>;
    Baseline baseline;
    unsigned low_mask = 0, high_mask = 0, high_size, low_size;
    Modulus high_mod, low_mod;
    typename detail::Weighted<K>::Plan high_plan;
    const unsigned *high_values = nullptr;
    const unsigned *low_values = nullptr;
    const std::uint64_t *high_digits = nullptr;

    Block(const Tables &t, const int *sorted_prefix, const int *suffix)
        : baseline(sorted_prefix, suffix), high_size(K - baseline.low_count),
          low_size(baseline.low_count), high_mod(f[high_size]),
          low_mod(f[low_size]) {
      for (int i = 0; i < K; ++i) {
        int v = sorted_prefix[i];
        if (v > M)
          high_mask |= 1u << (v - M - 1);
        else
          low_mask |= 1u << (v - 1);
      }
      low_values = t.direct_low[low_mask].data();
      if (high_size <= direct_limit)
        high_values = t.direct_high[high_mask].data();
      else if (high_size <= max_high) {
        high_digits = t.packed_high[high_size].data();
        high_plan = t.high_weights.plan(high_mask);
      }
    }
    template <class T>
    typename Baseline::Key key(Prefix prefix, const T *word) const {
      unsigned extra;
      if (high_values)
        extra = high_values[high_mod.of(prefix.high)];
      else if (high_digits)
        extra = high_plan(high_digits[high_mod.of(prefix.high)]);
      else if (!low_size)
        extra = f[K] - 1 - prefix.low;
      else
        return baseline.key(word);
      return {unsigned(baseline.head_base) + extra,
              unsigned(baseline.tail_base) + low_values[low_mod.of(prefix.low)],
              baseline.low_positions_fixed |
                  (low_positions<K>(word, low_size) << M)};
    }
  };
};
} // namespace quadrant_codes

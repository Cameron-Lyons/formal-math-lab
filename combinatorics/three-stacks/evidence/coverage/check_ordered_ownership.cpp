// Independently enumerate the ownership of every length-19 tail-order block.
// The only production modules used are the two encoders being cross-checked.
#include "quadrant.hpp"
#include "quadrant_codes.hpp"
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <stdexcept>
#include <vector>

namespace {
constexpr unsigned n = 19, cut = 11, length = 7, orders = 5040,
                   heads = 39916800;
constexpr std::array<unsigned, 8> factorial{1, 1, 2, 6, 24, 120, 720, 5040};
using Tail = std::array<unsigned, length>;
using Head = std::array<unsigned, cut>;
using Deck = std::array<int, n>;

unsigned order(const int *tail) {
  unsigned rank = 0;
  for (unsigned i = 0; i < length; ++i) {
    rank *= i + 1;
    for (unsigned j = 0; j < i; ++j)
      rank += tail[j] > tail[i];
  }
  return rank;
}

Deck dual(const Deck &p) {
  Deck d;
  for (unsigned i = 0; i < n; ++i)
    d[18 - p[i]] = 18 - i;
  return d;
}

struct Embedding {
  std::array<int, cut> front;
  Tail back;
  unsigned low;
};

std::vector<Embedding> embeddings() {
  std::vector<Embedding> choices;
  for (unsigned mask = 0; mask < 1u << 18; ++mask) {
    if (std::popcount(mask) != 7)
      continue;
    Embedding e;
    unsigned h = 0, t = 0;
    for (int v = 1; v <= 18; ++v) {
      if (mask & (1u << (v - 1)))
        e.back[t++] = v;
      else
        e.front[h++] = v;
    }
    e.low = mask & 127;
    choices.push_back(e);
  }
  return choices;
}

Deck physical(const Embedding &e, const Tail &t, const Head &h) {
  Deck p{};
  for (unsigned i = 0; i < cut; ++i)
    p[i] = e.front[h[i]];
  for (unsigned i = 0; i < length; ++i)
    p[cut + i] = e.back[t[i]];
  return p;
}

// For the seven low original labels only, record on which side of the cut
// they appear and their relative order on that side. Read in decreasing
// label order to obtain the positive suffix of the literal sorting dual.
unsigned mirrored_order(const Embedding &e, const Tail &tau, const Head &head) {
  std::array<int, 8> position{};
  for (unsigned i = 0; i < cut; ++i) {
    auto v = e.front[head[i]];
    if (v <= 7)
      position[v] = i;
  }
  for (unsigned i = 0; i < 7; ++i) {
    auto v = e.back[tau[i]];
    if (v <= 7)
      position[v] = cut + i;
  }
  int suffix[7];
  for (unsigned i = 0; i < 7; ++i)
    suffix[i] = 18 - position[7 - i];
  return order(suffix);
}

int audit(const char *policy_path, unsigned hard) {
  std::array<unsigned, orders> prio;
  prio.fill(orders);
  std::ifstream in(policy_path);
  for (unsigned i = 0; i < orders; ++i) {
    unsigned t, legacy;
    if (!(in >> t >> legacy) || t >= orders || legacy != 0 || prio[t] != orders)
      throw std::runtime_error("Invalid fresh rank policy");
    prio[t] = i;
  }
  auto mode = [&](unsigned t, unsigned d) {
    if (prio[t] < orders - hard)
      return 1u;
    if (t == d)
      return 2u;
    return unsigned(prio[t] < prio[d]);
  };
  std::array<Tail, orders> perm;
  std::array<int, 7> p;
  std::iota(p.begin(), p.end(), 0);
  do {
    auto &row = perm[order(p.data())];
    std::copy(p.begin(), p.end(), row.begin());
  } while (std::next_permutation(p.begin(), p.end()));
  const auto choices = embeddings();
  std::array<std::vector<unsigned>, 128> by_low;
  for (unsigned s = 0; s < choices.size(); ++s)
    by_low[choices[s].low].push_back(s);
  std::array<std::vector<unsigned>, 8> masks;
  for (unsigned mask = 0; mask < 128; ++mask)
    masks[7 - std::popcount(mask)].push_back(mask);
  constexpr uint64_t total = uint64_t(heads) * 31824;
  std::mt19937 rng(0x3b1926);
  uint64_t random_tests = 0, class_tests = 0, branches[8][3]{};
  auto check_physical = [&](unsigned tau, const Embedding &e,
                            const Head &word) {
    unsigned b = 7 - std::popcount(e.low);
    const auto &sample = choices[by_low[e.low].front()];
    const auto d = physical(e, perm[tau], word), mirror = dual(d);
    if (dual(mirror) != d)
      throw std::logic_error("Literal dual is not involutive");
    const unsigned actual = order(mirror.data() + cut);
    Head representative;
    std::iota(representative.begin(), representative.end(), 0);
    unsigned next = 0;
    for (auto v : word)
      if (v < b)
        representative[next++] = v;
    if (next != b)
      throw std::logic_error("Invalid rank subword");
    const Deck reference = physical(sample, perm[tau], representative);
    quadrant::Encoder<n, cut> encoder(sample.front.data(),
                                      reference.data() + cut);
    if (actual != encoder.key(representative.data()).order ||
        actual != mirrored_order(sample, perm[tau], representative) ||
        quadrant_codes::encode_prefix<cut>(word.data()).low % factorial[b] !=
            quadrant_codes::encode_prefix<cut>(representative.data()).low %
                factorial[b])
      throw std::logic_error(
          "A grouped representative has the wrong literal dual suffix or bin");
    unsigned m = mode(tau, actual), rev = mode(actual, tau);
    ++branches[b][m];
    ++random_tests;
    const bool owns = (m == 1 || (m == 2 && d <= mirror));
    const bool other = (rev == 1 || (rev == 2 && mirror <= d));
    if (!owns && !other)
      throw std::logic_error("Lost orbit");
    // Recompute exactly the two parts of the production lex test.
    auto pos = std::find(d.begin() + cut, d.end(), 18);
    auto mpos =
        pos == d.end()
            ? (std::max_element(word.begin(), word.end()) - word.begin())
            : pos - d.begin();
    int other_first = 18 - mpos;
    if ((m == 1 || (m == 2 && !(d.front() > other_first ||
                                (d.front() == other_first && mirror < d)))) !=
        owns)
      throw std::logic_error("Split lex pruning mismatch");
  };
  std::cout << "order,owned,delegated_or_bond,full,lex\n";
  for (unsigned tau = 0; tau < orders; ++tau) {
    for (unsigned b = 0; b <= 7; ++b) {
      const auto &m = masks[b];
      const auto &s = by_low[m[rng() % m.size()]];
      Head word;
      std::iota(word.begin(), word.end(), 0);
      std::shuffle(word.begin(), word.end(), rng);
      check_physical(tau, choices[s[rng() % s.size()]], word);
    }
    if (prio[tau] < orders - hard) {
      std::cout << tau << ',' << total << ",0," << total << ",0\n";
      continue;
    }
    std::array<unsigned, 128> usable{};
    std::array<const Embedding *, 128> first_usable{};
    for (const auto &e : choices) {
      // Count descending adjacent pairs of physical tail labels, including
      // the descending bond between the last positive card and terminal 0.
      int next = 0;
      bool bond = false;
      for (int i = 6; i >= 0; --i) {
        int x = e.back[perm[tau][i]];
        bond |= x == next + 1;
        next = x;
      }
      if (!bond && !usable[e.low]++)
        first_usable[e.low] = &e;
    }
    std::array<uint64_t, 3> count{};
    for (unsigned mask = 0; mask < 128; ++mask) {
      if (!usable[mask])
        continue;
      unsigned b = 7 - std::popcount(mask);
      const auto &e = choices[by_low[mask].front()];
      Head word;
      std::iota(word.begin(), word.end(), 0);
      const auto &actual = *first_usable[mask];
      const auto representative = physical(actual, perm[tau], word);
      quadrant::Encoder<n, cut> encoder(actual.front.data(),
                                        representative.data() + cut);
      std::vector<bool> used(factorial[b]);
      const uint64_t multiplicity =
          uint64_t(usable[mask]) * (heads / factorial[b]);
      do {
        unsigned d = mirrored_order(e, perm[tau], word);
        auto production = encoder.key(word.data()).order;
        auto code =
            quadrant_codes::encode_prefix<cut>(word.data()).low % factorial[b];
        if (production != d || used[code])
          throw std::logic_error(
              "Wrong dual label or repeated bin within grouped block");
        used[code] = true;
        ++class_tests;
        count[mode(tau, d)] += multiplicity;
      } while (std::next_permutation(word.begin(), word.begin() + b));
    }
    uint64_t owned = count[1] + count[2];
    std::cout << tau << ',' << owned << ',' << total - owned << ',' << count[1]
              << ',' << count[2] << '\n';
  }
  // Construct mutually paired layouts with each possible count of low
  // prefix cards. Rearranging high prefix letters preserves the mirrored
  // tail order, while allowing both comparisons at same-order ties.
  for (unsigned b = 0; b <= 7; ++b)
    for (unsigned j = 0; j < 1000; ++j) {
      std::array<int, 11> first;
      std::iota(first.begin(), first.end(), 0);
      std::array<int, 7> last;
      std::iota(last.begin(), last.end(), 11);
      std::shuffle(first.begin(), first.end(), rng);
      std::shuffle(last.begin(), last.end(), rng);
      Deck q;
      std::iota(q.begin(), q.end(), 0);
      for (unsigned i = 0; i < b; ++i)
        std::swap(q[first[i]], q[last[i]]);
      for (unsigned i = b + 1; i < 11; i += 2)
        if (rng() & 1)
          std::swap(q[first[i]], q[first[i - 1]]);
      for (unsigned i = b + 1; i < 7; i += 2)
        if (rng() & 1)
          std::swap(q[last[i]], q[last[i - 1]]);
      Deck p;
      for (unsigned i = 0; i < n; ++i)
        p[i] = 18 - q[i];
      Embedding e{};
      Head w;
      std::copy_n(p.begin(), cut, e.front.begin());
      std::sort(e.front.begin(), e.front.end());
      std::copy_n(p.begin() + cut, 7, e.back.begin());
      std::sort(e.back.begin(), e.back.end());
      for (unsigned v : e.back)
        if (v <= 7)
          e.low |= 1u << (v - 1);
      for (unsigned i = 0; i < cut; ++i)
        w[i] = std::lower_bound(e.front.begin(), e.front.end(), p[i]) -
               e.front.begin();
      for (unsigned i = 0; i < 15; ++i) {
        unsigned a = rng() % cut, z = rng() % cut;
        if (w[a] >= b && w[z] >= b)
          std::swap(w[a], w[z]);
      }
      check_physical(order(p.data() + cut), e, w);
    }
  std::cerr << "Exhaustive grouped classes " << class_tests << "\n";
  std::cerr << "Literal orientation tests " << random_tests << "\n";
  for (unsigned b = 0; b < 8; ++b)
    std::cerr << "b " << b << " omit " << branches[b][0] << " full "
              << branches[b][1] << " lex " << branches[b][2] << "\n";
  return 0;
}
} // namespace
int main(int argc, char **argv) {
  if (argc != 3)
    throw std::runtime_error(
        "usage: check_ordered_ownership fresh-priorities hard-count");
  return audit(argv[1], std::stoul(argv[2]));
}

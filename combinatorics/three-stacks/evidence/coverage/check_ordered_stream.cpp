// Validate actual length-19 candidates, rank membership and distinctness.
#include <algorithm>
#include <array>
#include <bit>
#include <charconv>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using Word = std::array<unsigned, 19>;

unsigned suffix(const Word& p) {
  unsigned rank = 0;
  unsigned seen = 0;
  for (unsigned i = 11; i < 18; i++) {
    rank = rank * (i - 10) + static_cast<unsigned>(std::popcount(seen >> p[i]));
    seen |= 1u << p[i];
  }
  return rank;
}

int main(int ac, char** av) {
  if (ac != 5) {
    throw std::runtime_error("input ranks_and_counts rank_priority hard_count");
  }
  std::ifstream src(av[1]);
  std::ifstream req(av[2]);
  std::ifstream order(av[3]);
  unsigned hard = static_cast<unsigned>(std::stoul(av[4]));
  if (!src || !req || !order || hard > 5040) {
    throw std::runtime_error("Invalid audit input");
  }
  std::array<int, 5040> priority;
  priority.fill(-1);
  for (int i = 0; i < 5040; i++) {
    unsigned t = 0;
    unsigned old = 0;
    if (!(order >> t >> old) || old || t >= 5040 || priority[t] != -1) {
      throw std::runtime_error("Expected fresh rank ordering");
    }
    priority[t] = i;
  }

  unsigned tau = 0;
  std::size_t count = 0;
  std::uint64_t total = 0;
  std::string line;
  while (req >> tau >> count) {
    if (tau >= 5040) {
      throw std::runtime_error("Invalid declared rank");
    }
    std::vector<std::uint64_t> ids;
    ids.reserve(count);
    for (std::size_t j = 0; j < count; j++) {
      if (!std::getline(src, line) || !line.starts_with("Hard 1 ")) {
        throw std::runtime_error("Incomplete or invalid candidate");
      }
      const char* start = line.data() + 7;
      const char* end = line.data() + line.size();
      Word p{};
      Word dual{};
      unsigned used = 0;
      std::uint64_t id = 0;
      for (unsigned i = 0; i < 19; i++) {
        unsigned val = 0;
        auto r = std::from_chars(start, end, val);
        if (r.ec != std::errc{} || val < 1 || val > 19) {
          throw std::runtime_error("Invalid card");
        }
        start = r.ptr;
        if (i < 18 && (start == end || *start++ != ' ')) {
          throw std::runtime_error("Invalid separator");
        }
        unsigned v = val - 1;
        unsigned bit = 1u << v;
        if ((used & bit) || (i && p[i - 1] == v + 1)) {
          throw std::runtime_error("Repeated label or descending bond");
        }
        unsigned digit = v - static_cast<unsigned>(std::popcount(used & (bit - 1)));
        id = id * (19 - i) + digit;
        used |= bit;
        p[i] = v;
        dual[18 - v] = 18 - i;
      }
      if (start != end || p.back() != 0 || suffix(p) != tau) {
        throw std::runtime_error("Wrong suffix rank");
      }
      if (static_cast<unsigned>(priority[tau]) >= 5040 - hard) {
        unsigned dt = suffix(dual);
        if (priority[dt] < priority[tau] || (dt == tau && dual < p)) {
          throw std::runtime_error("Wrong canonical orientation");
        }
      }
      ids.push_back(id);
    }
    std::sort(ids.begin(), ids.end());
    if (std::adjacent_find(ids.begin(), ids.end()) != ids.end()) {
      throw std::runtime_error("Duplicate candidate");
    }
    total += count;
  }
  if (!req.eof() || std::getline(src, line) || !src.eof()) {
    throw std::runtime_error("Unaccounted candidate or invalid rank file");
  }
  std::cout << "Checked " << total << " distinct, correctly assigned candidates\n";
}

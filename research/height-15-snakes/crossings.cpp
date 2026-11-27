// Independent edge-crossing dynamic program. Build with c++ -O3 -std=c++17.
// Run from a directory with scratch disk space. Scratch files are unlinked on open.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#include <unistd.h>

namespace {
constexpr int height = 15;
using Key = std::uint64_t;
using Word = std::uint32_t;
using Score = std::int16_t;
using Scores = std::vector<Score>;
constexpr Key done = ~Key(0);
constexpr Score unreachable = -1;

struct CloseFile {
    void operator()(std::FILE *file) const { std::fclose(file); }
};
using File = std::unique_ptr<std::FILE, CloseFile>;
File scratch_file() {
    char path[] = ".snake-crossings-XXXXXX";
    int fd = mkstemp(path);
    if (fd < 0) throw std::runtime_error("cannot create scratch file in current directory");
    unlink(path);
    std::FILE *file = fdopen(fd, "w+b");
    if (file == nullptr) {
        close(fd);
        throw std::runtime_error("cannot open scratch file stream");
    }
    return File(file);
}
void seek(std::FILE *file, off_t offset) {
    if (fseeko(file, offset, SEEK_SET) != 0) throw std::runtime_error("scratch seek failed");
}
template<class T> void write_all(std::FILE *file, const T *data, std::size_t size) {
    if (std::fwrite(data, sizeof(T), size, file) != size)
        throw std::runtime_error("scratch write failed");
}

// In geometric order along the cut, each of 16 positions is vacant (free),
// occupied without an edge across the cut (blocked), or crossed by a path end.
// The ends of unfinished paths form a noncrossing matching. Store each matched
// pair by an opening and a closing parenthesis. An unmatched crossing belongs
// to a path whose other end is already final. At row r, positions r and r+1
// are the incoming vertical and horizontal edges. They are replaced in place
// by the outgoing horizontal and vertical edges, respectively.
constexpr int blocked = 0, open = 16, close_pair = 32, single = 48;
constexpr Key column = 0x0001000100010001ULL;
constexpr unsigned mask16 = 65535;
Key bit(int lane, int pos) { return Key(1) << (lane + pos); }
int partner(Key key, int pos) {
    const unsigned openings = unsigned(key >> open) & mask16;
    const unsigned closings = unsigned(key >> close_pair) & mask16;
    const unsigned posbit = 1u << pos;
    if (openings & posbit) {
        unsigned rest = (openings | closings) & ~(2 * posbit - 1);
        int depth = 1;
        while (rest) {
            const int j = __builtin_ctz(rest);
            depth += openings & (1u << j) ? 1 : -1;
            if (depth == 0) return j;
            rest &= rest - 1;
        }
    } else if (closings & posbit) {
        unsigned rest = (openings | closings) & (posbit - 1);
        int depth = 1;
        while (rest) {
            const int j = 31 - __builtin_clz(rest);
            depth += closings & (1u << j) ? 1 : -1;
            if (depth == 0) return j;
            rest ^= 1u << j;
        }
    } else {
        return -1;
    }
    throw std::logic_error("unbalanced crossing-edge matching");
}
Key wrap(Key key, int row) {
    // At the bottom the outgoing vertical slot is empty. Move that empty slot
    // to the front for the next column, shifting all four bit planes together.
    return row + 1 == height && key != done ? key << 1 : key;
}

struct Moves {
    std::array<Key, 5> keys{};
    int size = 0;
    bool has_vacant = false;
    void vacant(Key key) { keys[size++] = key; has_vacant = true; }
    void occupied(Key key) { keys[size++] = key; }
};
Moves transitions(Key key, int row) {
    Moves moves;
    if (key == done) {
        moves.vacant(done);
        return moves;
    }
    const unsigned incoming_slots = 3u << row;
    const unsigned crossed = unsigned((key >> open) | (key >> close_pair) | (key >> single));
    const unsigned incoming = crossed & incoming_slots;
    Key cleared = key & ~(column * incoming_slots);
    if (incoming == 0) moves.vacant(wrap(cleared, row));
    if (key & incoming_slots) return moves; // An occupied old neighbor forbids filling here.

    const int up_mate = partner(key, row);
    const int left_mate = partner(key, row + 1);
    if (up_mate == row + 1) return moves; // Closing a cycle.
    if (up_mate >= 0) cleared &= ~(column << up_mate);
    if (left_mate >= 0) cleared &= ~(column << left_mate);
    const int in_degree = __builtin_popcount(incoming);
    for (int outgoing = 0; outgoing < 4; ++outgoing) {
        const bool right = outgoing & 1, down = outgoing & 2;
        if (down && row + 1 == height) continue;
        if (in_degree + right + down > 2) continue;
        Key result = cleared;
        if (!right) result |= bit(blocked, row);
        if (!down && row + 1 < height) result |= bit(blocked, row + 1);
        int ends[2], count = 0;
        if (up_mate >= 0) ends[count++] = up_mate;
        if (left_mate >= 0) ends[count++] = left_mate;
        if (right) ends[count++] = row;
        if (down) ends[count++] = row + 1;
        if (count == 2) {
            result |= bit(open, std::min(ends[0], ends[1]));
            result |= bit(close_pair, std::max(ends[0], ends[1]));
        } else if (count == 1) {
            result |= bit(single, ends[0]);
            if (__builtin_popcountll(result >> single) > 2) continue;
        } else {
            if (result >> open) continue; // A sealed component cannot rejoin.
            result = done;
        }
        moves.occupied(wrap(result, row));
    }
    return moves;
}

// Store keys in fixed-size chunks so that growing a layer never doubles its
// key storage. Hash collisions are resolved by exact 64-bit comparisons.
struct Layer {
    static constexpr int chunk_bits = 15;
    static constexpr int chunk_size = 1 << chunk_bits;
    std::vector<std::unique_ptr<Key[]>> chunks;
    std::vector<int> index;
    int count = 0, built = 0;
    File edges = scratch_file();

    Key at(int id) const { return chunks[id >> chunk_bits][id & (chunk_size - 1)]; }
    std::size_t bucket(Key key) const {
        Key hash = key ^ (key >> 30);
        hash *= 0xbf58476d1ce4e5b9ULL;
        hash ^= hash >> 27;
        hash *= 0x94d049bb133111ebULL;
        hash ^= hash >> 31;
        std::size_t pos = hash & (index.size() - 1);
        while (index[pos] >= 0 && at(index[pos]) != key)
            pos = (pos + 1) & (index.size() - 1);
        return pos;
    }
    int intern(Key key) {
        if (4 * std::size_t(count + 1) > 3 * index.size()) {
            index.assign(std::max<std::size_t>(16, 2 * index.size()), -1);
            for (int i = 0; i < count; ++i) index[bucket(at(i))] = i;
        }
        int &id = index[bucket(key)];
        if (id >= 0) return id;
        if (count >= (1 << 30) - 1) throw std::logic_error("state index overflow");
        if ((count & (chunk_size - 1)) == 0) chunks.emplace_back(new Key[chunk_size]);
        id = count++;
        chunks[id >> chunk_bits][id & (chunk_size - 1)] = key;
        return id;
    }
};
constexpr Word filled = Word(1) << 30, last = Word(1) << 31, empty = ~Word(0);
using Layers = std::array<Layer, height>;

void build(Layers &layers) {
    while (layers[0].built != layers[0].count) {
        for (int r = 0; r < height; ++r) {
            Layer &here = layers[r], &next = layers[(r + 1) % height];
            while (here.built < here.count) {
                Moves choices = transitions(here.at(here.built++), r);
                Word records[5] = {empty};
                for (int j = 0; j < choices.size; ++j) {
                    records[j] = Word(next.intern(choices.keys[j]));
                    if (j != 0 || !choices.has_vacant) records[j] |= filled;
                    if (j + 1 == choices.size) records[j] |= last;
                }
                write_all(here.edges.get(), records, std::max(1, choices.size));
            }
        }
        std::cerr << "Graph build reached " << layers[0].count << " column states.\n";
    }
}
// One record per valid transition. Every source has a final record, including
// a distinguished empty record for a state with no outgoing transition.
void advance(Layers &layers, Scores &scores) {
    std::array<Word, 32768> buffer;
    for (int r = 0; r < height; ++r) {
        Layer &layer = layers[r];
        Scores next(layers[(r + 1) % height].count, unreachable);
        std::FILE *file = layer.edges.get();
        seek(file, 0);
        std::size_t source = 0, records;
        while ((records = std::fread(buffer.data(), sizeof(Word), buffer.size(), file)) > 0) {
            for (std::size_t i = 0; i < records; ++i) {
                Word record = buffer[i];
                if (record != empty && scores[source] != unreachable) {
                    const int dest = int(record & (filled - 1));
                    Score value = Score(scores[source] + int(bool(record & filled)));
                    next[dest] = std::max(next[dest], value);
                }
                source += bool(record & last);
            }
        }
        if (std::ferror(file) || source != scores.size())
            throw std::runtime_error("incomplete transition file");
        scores.swap(next);
    }
}
std::uint64_t fingerprint(const Scores &scores, Score best) {
    std::uint64_t hash = 14695981039346656037ULL;
    for (std::size_t i = 0; i < scores.size(); i += 251) {
        hash ^= scores[i] == unreachable ? 65535u : unsigned(32767 + scores[i] - best);
        hash *= 1099511628211ULL;
    }
    return hash;
}
bool shifted(const Scores &earlier, const Scores &later, int gain) {
    for (std::size_t i = 0; i < earlier.size(); ++i) {
        int expected = earlier[i] == unreachable ? unreachable : earlier[i] + gain;
        if (later[i] != expected) return false;
    }
    return true;
}

constexpr int formula_start = 26;
int claimed_length(int width) {
    constexpr std::array<int, formula_start - 1> initial{
        15, 23, 32, 41, 49, 59, 68, 77, 87, 96, 105, 115, 123,
        134, 142, 152, 162, 171, 179, 190, 199, 208, 218, 227, 235};
    if (width < formula_start) return initial.at(width - 1);
    return (28 * width + 10) / 3;
}

void run(int limit) {
    Layers layers;
    const int start = layers[0].intern(0);
    build(layers);
    Layer &boundary = layers[0];
    const int finished = boundary.index[boundary.bucket(done)];
    if (finished < 0) throw std::logic_error("missing finished state");
    std::cout << "Column-boundary states = " << boundary.count << std::endl;
    for (auto &layer : layers) {
        layer.chunks.clear();
        std::vector<int>().swap(layer.index);
    }
    Scores scores(boundary.count, unreachable), previous(boundary.count);
    scores[start] = 0;
    std::vector<Score> bests{0};
    std::unordered_map<std::uint64_t, std::vector<int>> candidates;
    File history = scratch_file();
    const off_t bytes = off_t(scores.size()) * sizeof(Score);
    for (int width = 1; width <= limit; ++width) {
        advance(layers, scores);
        scores[start] = unreachable; // Require the snake to meet column one.
        Score best = scores[finished];
        if (best != claimed_length(width))
            throw std::logic_error("formula mismatch at width " + std::to_string(width));
        bests.push_back(best);
        std::cout << width << ' ' << best << std::endl;
        auto &widths = candidates[fingerprint(scores, best)];
        for (int earlier : widths) {
            seek(history.get(), (earlier - 1) * bytes);
            if (std::fread(previous.data(), sizeof(Score), previous.size(), history.get()) != previous.size())
                throw std::runtime_error("incomplete score file");
            int gain = best - bests[earlier];
            if (shifted(previous, scores, gain)) {
                const int period = width - earlier;
                if (earlier < formula_start || period % 3 != 0 || gain != 28 * (period / 3))
                    throw std::logic_error("shift does not propagate the claimed formula");
                auto reachable = scores.size() - std::count(scores.begin(), scores.end(), unreachable);
                std::cout << "D(" << width << ") = D(" << earlier << ") + " << gain
                          << " on all " << scores.size() << " states (" << reachable << " reachable).\n";
                return;
            }
        }
        widths.push_back(width);
        seek(history.get(), (width - 1) * bytes);
        write_all(history.get(), scores.data(), scores.size());
    }
    throw std::runtime_error("no repeated score vector within search limit");
}
} // namespace

int main(int argc, char **argv) {
    try {
        int limit = argc > 1 ? std::stoi(argv[1]) : 200;
        if (limit < 2 || limit > std::numeric_limits<Score>::max() / height)
            throw std::invalid_argument("search limit must be 2 through 2184");
        run(limit);
    } catch (std::exception const &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}

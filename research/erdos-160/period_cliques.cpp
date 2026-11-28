// Seven-colorings of [78] whose values repeat with the given period.
// Build: c++ -std=c++20 -O3 -march=native period_cliques.cpp -o period_cliques
// Run:   ./period_cliques 47                 (optionally pass a core dump filename)
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

using Mask = std::uint64_t;
using Pairs = std::array<Mask,64>;
constexpr int length = 78;
constexpr int palette = 7;

static Mask point(int x) { return Mask{1} << x; }
static int first(Mask m) { return std::countr_zero(m); }
static int size(Mask m) { return std::popcount(m); }

struct LargeClass {
    Mask set;
    Pairs forbidden{}; // Pairs that another color class must avoid.
};

struct Block {
    int index;
    Mask bits;
};

class PeriodSearch {
    int period, base, count = 0, words = 0;
    Mask universe;
    std::vector<Mask> progressions;
    Pairs forbidden_pairs{};
    std::array<Pairs,64> forbidden_triples{};
    std::vector<LargeClass> large;
    std::vector<std::size_t> row_offsets;
    std::array<std::array<int,64>,64> pair_id{};
    std::vector<Mask> containing;
    std::uint64_t uniform_nodes=0;
    std::vector<Mask> adjacency; // Only forward neighbors of each vertex.
    std::array<std::vector<Block>,palette+1> candidates;
    std::vector<int> clique;
    std::vector<Mask> witness;
    std::ofstream dump;
    std::map<std::pair<int,int>,std::uint64_t> core_counts;
    std::uint64_t small_rows = 0, partition_nodes = 0, covered_cores = 0;

    bool make_progressions() {
        for (int d=1; 3*d<length; ++d) for (int a=0; a+3*d<length; ++a) {
            Mask e = 0;
            for (int j=0; j<4; ++j) e |= point((a+j*d)%period);
            progressions.push_back(e);
        }
        std::sort(progressions.begin(),progressions.end());
        progressions.erase(std::unique(progressions.begin(),progressions.end()),progressions.end());
        for (Mask e : progressions) {
            int cardinality = size(e);
            if (cardinality < 3) return false;
            for (Mask i=e; i; i &= i-1) for (Mask j=i&(i-1); j; j &= j-1) {
                int x=first(i), y=first(j);
                if (cardinality==3) {
                    forbidden_pairs[x] |= point(y);
                    forbidden_pairs[y] |= point(x);
                } else {
                    // Any three equal colors on four positions already fail.
                    forbidden_triples[x][y] |= e ^ point(x) ^ point(y);
                    forbidden_triples[y][x] = forbidden_triples[x][y];
                }
            }
        }
        return true;
    }

    Pairs banned_by(Mask set) const {
        Pairs result{};
        for (Mask e : progressions) {
            Mask rest=e & ~set;
            if (size(rest)==2) {
                int x=first(rest), y=first(rest&(rest-1));
                result[x] |= point(y);
                result[y] |= point(x);
            }
        }
        return result;
    }

    // Each emitted set is a legal single color class. The additional pair
    // restrictions describe the previously selected color classes, if any.
    template<class Emit>
    void list_classes(Mask set, Mask available, const Pairs& pairs,
                      int minimum, int maximum, const Emit& emit) const {
        int k = size(set);
        if (k >= minimum) emit(set);
        if (k == maximum) return;
        while (available && k+size(available)>=minimum) {
            int v=first(available);
            available &= available-1;
            Mask next=available & ~pairs[v];
            for (Mask m=set; m; m &= m-1) next &= ~forbidden_triples[v][first(m)];
            list_classes(set|point(v),next,pairs,minimum,maximum,emit);
        }
    }

    void make_graph() {
        list_classes(0,universe,forbidden_pairs,base+1,period,[&](Mask s) {
            large.push_back({s,banned_by(s)});
        });
        std::sort(large.begin(),large.end(),[](const LargeClass& a,const LargeClass& b) {
            if (size(a.set)!=size(b.set)) return size(a.set)>size(b.set);
            return a.set<b.set;
        });
        count=static_cast<int>(large.size());
        words=(count+63)/64;

        int features=period;
        for(int i=0;i<period;++i)for(int j=i+1;j<period;++j)
            pair_id[i][j]=pair_id[j][i]=features++;
        containing.resize(std::size_t(features)*words);
        for(int id=0;id<count;++id) {
            auto mark=[&](int feature) {
                containing[std::size_t(feature)*words+id/64] |= point(id%64);
            };
            for(Mask r=large[id].set;r;r&=r-1) {
                int x=first(r); mark(x);
                for(Mask q=r&(r-1);q;q&=q-1) mark(pair_id[x][first(q)]);
            }
        }

        row_offsets.push_back(0);
        for(int id=0;id<count;++id) row_offsets.push_back(row_offsets.back()+words-id/64);
        adjacency.resize(row_offsets.back());
        std::uint64_t edge_count=0;
        for(int id=0;id<count;++id) {
            int begin=id/64;
            auto* row=adjacency.data()+row_offsets[id];
            std::fill(row,row+words-begin,~Mask{0});
            row[0] &= (~Mask{1}) << (id%64);
            if(count%64) row[words-begin-1] &= point(count%64)-1;
            auto exclude=[&](int feature) {
                const auto* banned=containing.data()+std::size_t(feature)*words+begin;
                for(int j=0;j<words-begin;++j) row[j] &= ~banned[j];
            };
            for(Mask r=large[id].set;r;r&=r-1) exclude(first(r));
            for(int x=0;x<period;++x) {
                for(Mask r=large[id].forbidden[x] & ~((point(x)-1)|point(x));r;r&=r-1)
                    exclude(pair_id[x][first(r)]);
            }
            for(int j=0;j<words-begin;++j) edge_count+=size(row[j]);
        }
        std::cout<<"large_classes="<<count<<" graph_edges="<<edge_count<<std::endl;
    }

    static bool allowed(Mask set, const Pairs& pairs) {
        for(Mask r=set;r;r&=r-1) if(pairs[first(r)] & set) return false;
        return true;
    }

    bool partition(Mask left, int seats, const std::vector<Mask>& rows) {
        ++partition_nodes;
        if (!seats) return !left;
        if (size(left)<seats || size(left)>seats*base) return false;
        int smallest=std::max(1,size(left)-(seats-1)*base);
        std::array<int,64> freq{};
        for(Mask row:rows) if(size(row)>=smallest) for(Mask m=row;m;m&=m-1) ++freq[first(m)];
        int position=first(left);
        for(Mask m=left;m;m&=m-1) if(freq[first(m)]<freq[position]) position=first(m);
        if (!freq[position]) return false;
        for(Mask row:rows) {
            if (!(row & point(position)) || size(row)<smallest) continue;
            Pairs banned=banned_by(row);
            std::vector<Mask> next;
            for(Mask other:rows) if(!(other&row) && allowed(other,banned)) next.push_back(other);
            witness.push_back(row);
            if(partition(left^row,seats-1,next)) return true;
            witness.pop_back();
        }
        return false;
    }

    bool has_class(Mask chosen, Mask available, const Pairs& pairs, int missing) const {
        if (!missing) return true;
        while (size(available) >= missing) {
            int v = first(available);
            available &= available - 1;
            Mask next = available & ~pairs[v];
            for (Mask m=chosen; m; m &= m-1) next &= ~forbidden_triples[v][first(m)];
            if (has_class(chosen|point(v),next,pairs,missing-1)) return true;
        }
        return false;
    }

    bool finish_with_small(Mask used, int seats, int excess) {
        ++core_counts[{palette-seats,excess}];
        if(dump.is_open()) {
            dump<<clique.size();
            for(int id:clique) dump<<' '<<large[id].set;
            dump<<'\n';
        }
        Mask left=universe^used;
        if (!seats) return !left;
        if (size(left)<seats) return false;
        Pairs pairs=forbidden_pairs;
        for(int id:clique) for(int i=0;i<period;++i) pairs[i]|=large[id].forbidden[i];
        int minimum=std::max(1,size(left)-(seats-1)*base);
        // A point with too few compatible neighbors cannot be covered by a
        // sufficiently large small class. Test the most restricted points first.
        std::array<std::pair<int,int>,64> points;
        int number=0;
        for (Mask m=left; m; m &= m-1) {
            int x=first(m), degree=size(left & ~pairs[x])-1;
            if (degree < minimum-1) return false;
            points[number++]={degree,x};
        }
        std::sort(points.begin(),points.begin()+number);
        for (int j=0;j<number;++j) {
            int x=points[j].second;
            if (!has_class(point(x),left & ~pairs[x] & ~point(x),pairs,minimum-1)) return false;
        }
        std::vector<Mask> rows;
        Mask covered=0;
        list_classes(0,left,pairs,minimum,base,[&](Mask s) {rows.push_back(s);covered|=s;});
        small_rows+=rows.size();
        if (covered!=left) return false;
        ++covered_cores;
        return partition(left,seats,rows);
    }

    bool adjacent(int a,int b) const {
        if (a>b) std::swap(a,b);
        return adjacency[row_offsets[a]+b/64-a/64] & point(b%64);
    }

    // A large domain is cheaper to filter in machine words. This row includes
    // both directions, so the completion search may branch on any uncovered point.
    void symmetric_neighbors(int id, std::vector<Mask>& out) const {
        auto exclude=[&](int feature){
            auto* bad=containing.data()+std::size_t(feature)*words;
            for(int j=0;j<words;++j)out[j] &= ~bad[j];
        };
        for(Mask m=large[id].set;m;m&=m-1) exclude(first(m));
        for(int x=0;x<period;++x) {
            for(Mask m=large[id].forbidden[x] & ~((point(x)-1)|point(x));m;m&=m-1)
                exclude(pair_id[x][first(m)]);
        }
    }

    bool equal_sizes(Mask left,int seats,const std::vector<int>& domain) {
        ++uniform_nodes;
        if(!seats) return !left;
        if(domain.size()<std::size_t(seats)) return false;
        if(seats==1) {
            for(int id:domain) if(large[id].set==left) {
                witness.push_back(left);return true;
            }
            return false;
        }
        std::array<int,64> support{};
        for(int id:domain) for(Mask m=large[id].set;m;m&=m-1) ++support[first(m)];
        int x=first(left);
        for(Mask m=left;m;m&=m-1) if(support[first(m)]<support[x]) x=first(m);
        if(!support[x]) return false;
        std::vector<int> next;
        std::vector<Mask> domain_bits;
        if(domain.size()>6000) {
            domain_bits.resize(words);
            for(int id:domain) domain_bits[id/64]|=point(id%64);
        }
        for(int id:domain) if(large[id].set & point(x)) {
            next.clear();
            if(domain_bits.empty()) {
                for(int j:domain) if(adjacent(id,j)) next.push_back(j);
            } else {
                auto usable=domain_bits;symmetric_neighbors(id,usable);
                for(int j=0;j<words;++j)for(Mask m=usable[j];m;m&=m-1)
                    next.push_back(64*j+first(m));
            }
            witness.push_back(large[id].set);
            if(equal_sizes(left^large[id].set,seats-1,next)) return true;
            witness.pop_back();
        }
        return false;
    }

    bool search(Mask used, int depth) {
        int seats=palette-depth, excess=size(used)-base*depth;
        int need=period-base*palette-excess;
        if(need<=0 && finish_with_small(used,seats,excess)) return true;
        if(!seats) return false;
        const auto& active=candidates[depth];

        // The first 'seats' candidates have largest size. Even without any
        // compatibility restrictions their excess must reach the threshold.
        int available=seats, bound=0, required=0;
        for(auto block:active) {
            for(Mask m=block.bits;m && available;m&=m-1) {
                if (bound<need) ++required;
                bound+=size(large[64*block.index+first(m)].set)-base;
                --available;
            }
            if (!available) break;
        }
        if(bound<need) return false;
        if (depth>=2 && need>0) {
            // At most seats-required more classes can be small. Everything else
            // must appear among the remaining large candidates.
            int allowance=(seats-required)*base;
            Mask missing=universe^used;
            for(auto block:active) {
                for(Mask m=block.bits;m && size(missing)>allowance;m&=m-1)
                    missing &= ~large[64*block.index+first(m)].set;
                if(size(missing)<=allowance)break;
            }
            if(size(missing)>allowance)return false;
        }

        auto& next=candidates[depth+1];
        for(std::size_t k=0;k<active.size();++k) {
            const auto block=active[k];
            for(Mask m=block.bits;m;m&=m-1) {
                int id=64*block.index+first(m);
                if((size(large[id].set)-base)*seats<need) return false;
                if(size(large[id].set)*seats==period-size(used)) {
                    // Smaller classes cannot cover the residual points. Select
                    // equally large rows by the least-supported point instead.
                    std::vector<int> domain;
                    for(std::size_t t=k;t<active.size();++t) {
                        for(Mask a=(t==k?m:active[t].bits);a;a&=a-1) {
                            int other=64*active[t].index+first(a);
                            if(size(large[other].set)==size(large[id].set))domain.push_back(other);
                        }
                    }
                    return equal_sizes(universe^used,seats,domain);
                }
                if (!depth) {
                    if(id%5000==0)std::cerr<<"root "<<id<<'/'<<count<<'\n';
                    // Either orientation of a putative partition can be used.
                    // Choose the one with the smaller first largest class.
                    Mask reflected=0;
                    for(Mask r=large[id].set; r; r &= r-1)
                        reflected |= point((length-1-first(r))%period);
                    if(reflected<large[id].set)continue;
                }
                const auto* row=adjacency.data()+row_offsets[id];
                next.clear();
                for(std::size_t q=k;q<active.size();++q) {
                    auto b=active[q];
                    Mask keep=b.bits & row[b.index-block.index];
                    if(keep) next.push_back({b.index,keep});
                }
                clique.push_back(id);
                if(search(used|large[id].set,depth+1)) return true;
                clique.pop_back();
            }
        }
        return false;
    }

public:
    PeriodSearch(int p,const char* file) : period(p),base((p-1)/palette),universe(point(p)-1) {
        if (file) {dump.open(file);if(!dump)throw std::runtime_error("cannot open core dump");}
    }
    void run() {
        if(!make_progressions()) {std::cout<<"fewer than three residues in a progression\n";return;}
        make_graph();
        for(int j=0;j<words;++j) {
            Mask bits=~Mask{0};
            if(j==words-1 && count%64)bits=point(count%64)-1;
            candidates[0].push_back({j,bits});
        }
        bool found=search(0,0);
        if(found) {
            for(int id:clique)witness.push_back(large[id].set);
            if(witness.size()!=palette)throw std::logic_error("wrong color count");
            Mask union_of_classes = 0;
            for (Mask c : witness) {
                if (!c || (union_of_classes & c)) throw std::logic_error("classes overlap or are empty");
                union_of_classes |= c;
            }
            if (union_of_classes != universe) throw std::logic_error("classes do not cover");
            for(Mask e:progressions) {
                int colors=0;for(Mask row:witness) if(row&e)++colors;
                if(colors<3)throw std::logic_error("invalid witness");
            }
            for(int x=0;x<length;++x) for(int i=0;i<palette;++i)
                if(witness[i]&point(x%period))std::cout<<i<<' ';
            std::cout<<'\n';
        }
        for(auto [key,n]:core_counts)
            std::cout<<"large_count="<<key.first<<" excess="<<key.second<<" cores="<<n<<'\n';
        std::cout<<"p="<<period<<" base="<<base<<" small_classes="<<small_rows
                 <<" uniform_nodes="<<uniform_nodes<<" covered_cores="<<covered_cores<<" partition_nodes="<<partition_nodes
                 <<" seven_colors="<<(found?"yes":"no")<<std::endl;
    }
};

int main(int argc,char** argv) {
    if(argc>3)return 2;
    int p=argc>1?std::stoi(argv[1]):47;
    if(p<7 || p>63)throw std::invalid_argument("period must be in [7,63]");
    PeriodSearch(p,argc==3?argv[2]:nullptr).run();
}

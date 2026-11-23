// Exhaustive reduced-ANF / geometric-validity comparison on binary height five.
#include <bit>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

struct Substitution { unsigned cell; uint32_t mask; unsigned constant; };

int main(int argc,char** argv) {
    if (argc!=2) return 2;
    std::ifstream in(argv[1]);
    unsigned n,m; in>>n>>m;
    if (!in || n!=21 || m!=11) return 2;
    std::vector<unsigned> free(n);
    for (auto& v:free) in>>v;
    unsigned count; in>>count;
    std::vector<Substitution> substitutions;
    for (unsigned i=0;i<count;++i) {
        Substitution sub; std::string mask;
        in>>sub.cell>>mask>>sub.constant;
        sub.mask=std::stoul(mask,nullptr,16); substitutions.push_back(sub);
    }
    std::vector<std::vector<uint32_t>> equations(m);
    for (auto& equation:equations) {
        unsigned size; in>>size;
        for (unsigned i=0;i<size;++i) {
            std::string mask; in>>mask;
            equation.push_back(std::stoul(mask,nullptr,16));
        }
    }
    if (!in) return 2;
    uint64_t solutions=0,checked=0;
    auto start=std::chrono::steady_clock::now();
    for (uint32_t assignment=0;assignment<(1u<<n);++assignment) {
        uint32_t board=0;
        for (unsigned i=0;i<n;++i) board|=((assignment>>i)&1u)<<free[i];
        for (auto sub:substitutions)
            board|=((std::popcount(assignment&sub.mask)&1u)^sub.constant)<<sub.cell;
        uint32_t seen=0; bool geometric=true;
        for (unsigned r=1;r<5 && geometric;++r) for (unsigned j=0;j<2*r-1;++j) {
            unsigned t=(board>>((r-1)*(r-1)+j))&1u;
            unsigned lower=(board>>(r*r+j))&7u;
            unsigned pattern=(t<<3)|lower;
            if (seen>>pattern&1u) { geometric=false; break; }
            seen|=1u<<pattern;
        }
        bool algebraic=true;
        for (const auto& equation:equations) {
            unsigned value=0;
            for (auto term:equation) value^=((assignment&term)==term);
            if (value) { algebraic=false; break; }
        }
        if (algebraic!=geometric) {
            std::cerr<<"MISMATCH assignment="<<assignment<<'\n'; return 1;
        }
        solutions+=algebraic; ++checked;
    }
    double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
    std::cout<<"{\"status\":\"COMPLETE\",\"free_boolean_variables\":"<<n
        <<",\"assignments_checked\":"<<checked<<",\"solutions\":"<<solutions
        <<",\"geometric_anf_mismatches\":0,\"seconds\":"<<seconds<<"}\n";
    return solutions==168?0:1;
}

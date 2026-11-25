// Scan valid ternary boards for a two-cell swap preserving all 3-marginals.
// Build: c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_structure_switch.cpp -o /tmp/exact_structure_switch
// Input: one flattened 100-digit ternary board per line.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
struct Window { std::array<int,4> cells; };
struct Incidence { int placement, axis; };
struct Signature { int cell, color, parity; unsigned oldmask, newmask; };
int main() {
    std::vector<Window> windows;
    std::array<std::vector<Incidence>,100> incidence;
    for (int r=1;r<10;++r) for (int j=0;j<2*r-1;++j) {
        Window w{{(r-1)*(r-1)+j,r*r+j,r*r+j+1,r*r+j+2}};
        int i=windows.size(); windows.push_back(w);
        for (int a=0;a<4;++a) incidence[w.cells[a]].push_back({i,a});
    }
    std::array<std::array<int,81>,3> binary_code;
    constexpr std::array<std::array<int,2>,3> palettes{{{0,1},{0,2},{1,2}}};
    for (int p=0;p<3;++p) for (int c=0;c<81;++c) {
        int x=c,bin=0; bool okay=true;
        for (int k=0;k<4;++k) { int digit=x%3; x/=3;
            if (digit!=palettes[p][0] && digit!=palettes[p][1]) okay=false;
            if (digit==palettes[p][1]) bin|=1<<k;
        }
        binary_code[p][c]=okay?bin:-1;
    }
    std::string board; std::uint64_t checked=0;
    while (std::cin>>board) {
        if (board.size()!=100 || board.find_first_not_of("012")!=std::string::npos) return 2;
        std::array<int,81> codes{};
        for (int i=0;i<81;++i) for (int c:windows[i].cells) codes[i]=3*codes[i]+board[c]-'0';
        for (int p=0;p<3;++p) {
            std::vector<Signature> prior;
            for (int c=0;c<100;++c) {
                if (incidence[c].size()!=4) continue;
                int color=board[c]-'0';
                if (color!=palettes[p][0] && color!=palettes[p][1]) continue;
                unsigned oldmask=0,newmask=0; int parity=-1;
                bool okay=true;
                for (auto [i,a]:incidence[c]) {
                    int bin=binary_code[p][codes[i]];
                    if (bin<0) {okay=false; break;}
                    int q=std::popcount(unsigned(bin))%2;
                    if (parity!=-1 && parity!=q) {okay=false; break;}
                    parity=q; oldmask|=1u<<bin; newmask|=1u<<(bin^(1<<(3-a)));
                }
                if (!okay || std::popcount(oldmask)!=4 || std::popcount(newmask)!=4) continue;
                unsigned total=parity?0x6996u:0x9669u;
                for (auto previous:prior) {
                    if (previous.color==color || previous.parity!=parity) continue;
                    if ((previous.oldmask^oldmask)==total && (previous.newmask^newmask)==(65535u^total)) {
                        std::cout<<"FOUND "<<checked<<' '<<previous.cell<<' '<<c<<' '<<p<<' '<<parity<<'\n';
                        std::cout<<board<<'\n'; std::swap(board[previous.cell],board[c]);
                        std::cout<<board<<'\n'; return 0;
                    }
                }
                prior.push_back({c,color,parity,oldmask,newmask});
            }
        }
        ++checked;
    }
    std::cout<<"NONE checked="<<checked<<'\n';
}

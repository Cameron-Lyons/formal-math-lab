// Independent flat Cartesian enumeration: no pruning and no rotor DFS reused.
#include <array>
#include <cstdint>
#include <iostream>
#include <map>

int main() {
    constexpr int q=3, h=4, cells=16, windows=9;
    std::array<std::array<int,4>,windows> placements{};
    int w=0;
    // A row r has centered coordinates -r,...,r and starts at cell r^2.
    for (int r=1;r<h;++r)
        for (int x=-r+1;x<=r-1;++x)
            placements[w++] = {(r-1)*(r-1)+x+r-1,
                               r*r+x-1+r,r*r+x+r,r*r+x+1+r};
    std::map<std::array<int,4>,uint64_t> histogram;
    uint64_t cap_count=0,total=1;
    for(int i=1;i<cells;++i)total*=q;
    for (uint64_t code=0;code<total;++code) {
        std::array<int,cells> color{};
        uint64_t value=code;
        for(int i=1;i<cells;++i){color[i]=value%q;value/=q;}
        std::array<uint64_t,2> seen{};
        std::array<int,27> multiplicities{};
        bool valid=true;
        for(const auto &p:placements){
            int triple=(color[p[0]]*q+color[p[1]])*q+color[p[2]];
            int quadruple=triple*q+color[p[3]];
            uint64_t bit=uint64_t(1)<<(quadruple%64);
            if(seen[quadruple/64]&bit){valid=false;break;}
            seen[quadruple/64]|=bit;
            ++multiplicities[triple];
        }
        if(!valid)continue;
        std::array<int,4> frequencies{};
        for(int count:multiplicities)++frequencies[count];
        ++histogram[frequencies];++cap_count;
    }
    std::cout<<"{\"status\":\"COMPLETE_FINITE_CAP_ENUMERATION\",\"apex\":0,"
             <<"\"assignments_examined\":"<<total<<",\"caps\":"<<cap_count<<",\"histogram\":[";
    bool first=true;
    for(const auto &[frequencies,count]:histogram){
        if(!first)std::cout<<',';
        first=false;
        std::cout<<"{\"n0\":"<<frequencies[0]<<",\"n1\":"<<frequencies[1]
                 <<",\"n2\":"<<frequencies[2]<<",\"n3\":"<<frequencies[3]
                 <<",\"caps\":"<<count<<'}';
    }
    std::cout<<"]}\n";
}

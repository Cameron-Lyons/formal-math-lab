// Exhaustive distinct-pattern caps, apex fixed to0; constant-memory rotor histogram.
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <ctime>
#include <iostream>
#include <string>
#include <sys/resource.h>

struct Bin { uint64_t caps=0; int n2=0,n3=0; };
int q,height,cell_count,triple_count,windows;
std::array<int,100> cells{},top{};
std::array<bool,81> used{};
std::array<int,27> usage{};
std::array<int,4> frequency{};
std::array<std::array<Bin,28>,28> histogram{};
uint64_t nodes=0,leaves=0,rejected=0;

void visit(int position) {
    ++nodes;
    if (position==cell_count) {
        assert(frequency[0]+frequency[1]+frequency[2]+frequency[3]==triple_count);
        assert(frequency[1]+2*frequency[2]+3*frequency[3]==windows);
        Bin &bin=histogram[frequency[0]][frequency[1]];
        if (!bin.caps) { bin.n2=frequency[2];bin.n3=frequency[3]; }
        else { assert(bin.n2==frequency[2] && bin.n3==frequency[3]); }
        ++bin.caps;++leaves;return;
    }
    if (position<2 || top[position]<0) {
        for (int color=0;color<q;++color) { cells[position]=color;visit(position+1); }
        return;
    }
    const int triple=(cells[top[position]]*q+cells[position-2])*q+cells[position-1];
    const int old_count=usage[triple];
    for (int color=0;color<q;++color) {
        const int pattern=triple*q+color;
        if (used[pattern]) { ++rejected;continue; }
        assert(old_count<q);
        cells[position]=color;used[pattern]=true;
        usage[triple]=old_count+1;--frequency[old_count];++frequency[old_count+1];
        visit(position+1);
        usage[triple]=old_count;--frequency[old_count+1];++frequency[old_count];
        used[pattern]=false;
    }
}

int main(int argc,char**argv) {
    if (argc!=3) { std::cerr<<"usage: census colors height\n";return 2; }
    q=std::stoi(argv[1]);height=std::stoi(argv[2]);
    if (!((q==2 && height>=1 && height<=5)||(q==3 && height>=1 && height<=4))) {
        std::cerr<<"bounded to binary heights1..5 or ternary heights1..4\n";return 2;
    }
    cell_count=height*height;triple_count=q*q*q;windows=(height-1)*(height-1);
    top.fill(-1);
    for (int row=1;row<height;++row)
        for (int start=0;start<2*row-1;++start)
            top[row*row+start+2]=(row-1)*(row-1)+start;
    frequency[0]=triple_count;cells[0]=0;
    const auto started=std::chrono::steady_clock::now();const auto cpu_started=std::clock();
    visit(1);
    const auto elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();
    const auto cpu=double(std::clock()-cpu_started)/CLOCKS_PER_SEC;
    struct rusage memory{};getrusage(RUSAGE_SELF,&memory);
    std::cout<<"{\"colors\":"<<q<<",\"height\":"<<height<<",\"apex\":0,\"cells\":"<<cell_count
      <<",\"placements\":"<<windows<<",\"known_boundary_cells\":"<<2*height-1
      <<",\"caps\":"<<leaves<<",\"nodes\":"<<nodes<<",\"duplicate_pattern_rejections\":"<<rejected
      <<",\"wall_seconds\":"<<elapsed<<",\"cpu_seconds\":"<<cpu
      <<",\"peak_rss_kib\":"<<memory.ru_maxrss<<",\"histogram\":[";
    bool first=true;
    for (int n0=0;n0<=triple_count;++n0) for (int n1=0;n1<=triple_count;++n1) {
        const Bin&bin=histogram[n0][n1];if (!bin.caps)continue;
        if (!first)std::cout<<',';
        first=false;
        std::cout<<"{\"n0\":"<<n0<<",\"n1\":"<<n1<<",\"n2\":"<<bin.n2<<",\"n3\":"<<bin.n3<<",\"caps\":"<<bin.caps<<'}';
    }
    std::cout<<"]}\n";
}

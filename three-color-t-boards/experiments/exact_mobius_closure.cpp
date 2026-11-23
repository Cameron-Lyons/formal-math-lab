// Exact collision-event inclusion-exclusion, aggregated by cell partition.
// A state/time cap reports INCOMPLETE, never a polynomial for the full board.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

using Clock = std::chrono::steady_clock;
using Window = std::array<int,4>;
using Table = std::unordered_map<std::string,int64_t>;

static std::string merge(const std::string& state, const Window& a,
                         const Window& b) {
    int parent[25], label[25];
    for (int i=0;i<25;++i) { parent[i]=i; label[i]=-1; }
    auto root=[&](int x) { while (parent[x]!=x) x=parent[x]; return x; };
    for (int k=0;k<4;++k) parent[root(state[b[k]])]=root(state[a[k]]);
    std::string result=state; int next=0;
    for (size_t i=0;i<state.size();++i) {
        int r=root(state[i]);
        if (label[r]<0) label[r]=next++;
        result[i]=static_cast<char>(label[r]);
    }
    return result;
}

int main(int argc,char** argv) {
    int h=argc>1?std::stoi(argv[1]):4;
    size_t cap=argc>2?std::stoull(argv[2]):500000;
    double seconds=argc>3?std::stod(argv[3]):30;
    if (h<1 || h>5 || cap<1 || seconds<=0) return 2;
    // For <=16 placements, all intermediate coefficient absolute sums are
    // <=16!: each prefix is a graph's collision arrangement, and its
    // unaggregated absolute sum is the graph's acyclic orientation count.
    std::vector<Window> windows;
    for (int r=1;r<h;++r) for (int j=0;j<2*r-1;++j)
        windows.push_back({(r-1)*(r-1)+j,r*r+j,r*r+j+1,r*r+j+2});
    std::vector<std::array<int,2>> events;
    for (int j=1;j<(int)windows.size();++j)
        for (int i=0;i<j;++i) events.push_back({i,j});
    std::string initial(h*h,'\0');
    for (int i=0;i<h*h;++i) initial[i]=static_cast<char>(i);
    Table states; states.emplace(initial,1);
    auto start=Clock::now();
    auto elapsed=[&]() { return std::chrono::duration<double>(Clock::now()-start).count(); };
    size_t peak=1; int processed=0;
    for (auto event:events) {
        Table next=states; next.reserve(std::min(cap,states.size()*2));
        size_t visited=0;
        for (const auto& [state,coefficient]:states) {
            auto joined=merge(state,windows[event[0]],windows[event[1]]);
            auto [it,inserted]=next.try_emplace(std::move(joined),0);
            it->second-=coefficient;
            if (it->second==0) next.erase(it);
            if (next.size()>cap || ((++visited&8191)==0 && elapsed()>seconds)) {
                std::cout << "{\"status\":\"INCOMPLETE\",\"height\":" << h
                    << ",\"completed_events\":" << processed
                    << ",\"total_events\":" << events.size()
                    << ",\"last_complete_states\":" << states.size()
                    << ",\"partial_states\":" << next.size()
                    << ",\"reason\":\"" << (next.size()>cap?"state_cap":"time_cap")
                    << "\",\"seconds\":" << elapsed() << "}\n";
                return 0;
            }
        }
        states=std::move(next); ++processed; peak=std::max(peak,states.size());
        std::cerr << "events=" << processed << '/' << events.size()
            << " nonzero_closures=" << states.size() << " seconds=" << elapsed() << '\n';
        if (elapsed()>seconds && processed<(int)events.size()) {
            std::cout << "{\"status\":\"INCOMPLETE\",\"height\":" << h
                << ",\"completed_events\":" << processed
                << ",\"total_events\":" << events.size()
                << ",\"last_complete_states\":" << states.size()
                << ",\"reason\":\"time_cap\",\"seconds\":" << elapsed() << "}\n";
            return 0;
        }
    }
    std::map<int,int64_t> polynomial;
    for (const auto& [state,coefficient]:states)
        polynomial[1+*std::max_element(state.begin(),state.end())]+=coefficient;
    std::cout << "{\"status\":\"COMPLETE\",\"height\":" << h
        << ",\"events\":" << events.size()
        << ",\"nonzero_closures\":" << states.size()
        << ",\"peak_nonzero_closures\":" << peak
        << ",\"seconds\":" << elapsed() << ",\"coefficients\":{";
    bool first=true;
    for (auto [degree,coefficient]:polynomial) if (coefficient) {
        if (!first) std::cout << ',';
        first=false; std::cout << '\"' << degree << "\":" << coefficient;
    }
    std::cout << "}}\n";
}

#include "exact_tworow_core.hpp"
#include <iostream>
#include <string>
#include <ctime>
template<int Q>int run(int depth,size_t capacity,double seconds,bool endpoints){
 constexpr int H=Q*Q+1,L=2*Q*Q-3,T=Q*Q*Q;TwoRows<Q> solver(depth,capacity,endpoints);std::string prefix;
 while(std::cin>>prefix){if(prefix.size()!=size_t((H-2)*(H-2)))throw std::invalid_argument("wrong prefix length");for(char c:prefix)if(c<'0'||c>='0'+Q)throw std::invalid_argument("invalid prefix color");
  std::array<unsigned,3> edges{};for(int c=0;c<Q;++c)edges[c]=(1u<<T)-1;bool valid=true;
  for(int r=1;r<H-2;++r)for(int j=0;j<2*r-1;++j){int t=prefix[(r-1)*(r-1)+j]-'0',code=(prefix[r*r+j]-'0')*Q*Q+(prefix[r*r+j+1]-'0')*Q+prefix[r*r+j+2]-'0';unsigned bit=1u<<code;if(!(edges[t]&bit))valid=false;edges[t]&=~bit;}
  std::array<int,L> top{};for(int j=0;j<L;++j)top[j]=prefix[(H-3)*(H-3)+j]-'0';
  auto start=std::chrono::steady_clock::now();auto cpu=std::clock();auto old_nodes=solver.nodes,old_calls=solver.terminal_calls,old_hits=solver.hits;
  uint64_t count=valid?solver.count(top.data(),edges,seconds):0;
  std::cout<<"status="<<(solver.timeout?"INCOMPLETE":"COMPLETE")<<" count="<<count<<" nodes="<<solver.nodes-old_nodes<<" terminal_calls="<<solver.terminal_calls-old_calls<<" memo_hits="<<solver.hits-old_hits<<" entries="<<solver.entries()<<" cpu_seconds="<<double(std::clock()-cpu)/CLOCKS_PER_SEC<<" elapsed="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<'\n';
  if(solver.timeout)return 1;
 }
 std::cerr<<"requests="<<solver.requests<<" nodes="<<solver.nodes<<" terminal_calls="<<solver.terminal_calls<<" initial_pairs="<<solver.initial_pairs<<" entries="<<solver.entries()<<" lookups="<<solver.lookups<<" hits="<<solver.hits<<'\n';return 0;
}
int main(int argc,char**argv){try{int q=argc>1?std::stoi(argv[1]):3,depth=argc>2?std::stoi(argv[2]):0;size_t cap=argc>3?std::stoull(argv[3]):1000000;double seconds=argc>4?std::stod(argv[4]):90;bool endpoints=argc>5?std::stoi(argv[5])!=0:true;if(q==2)return run<2>(depth,cap,seconds,endpoints);if(q==3)return run<3>(depth,cap,seconds,endpoints);throw std::invalid_argument("colors must be2 or3");}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}

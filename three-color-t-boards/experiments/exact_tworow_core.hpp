#pragma once
// Exact interleaved transfer for the last two rows of a q-color T board.
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <stdexcept>
#include <unordered_map>
using TwoBits=__uint128_t;
struct TwoHash {size_t operator()(TwoBits x)const{uint64_t a=x,b=x>>64;a^=b+0x9e3779b97f4a7c15ULL+(a<<6)+(a>>2);a^=a>>30;a*=0xbf58476d1ce4e5b9ULL;a^=a>>27;a*=0x94d049bb133111ebULL;return a^(a>>31);}};
template<int Q> class TwoRows {
 static_assert(Q==2||Q==3);
 static constexpr int L=2*Q*Q-3,T=Q*Q*Q,PAIRS=Q*Q;
 std::array<int,L> top{};
 std::array<unsigned,3> edges{};
 std::array<int,Q> quota{};
 unsigned end_first=0;std::array<unsigned,Q>end_second{};
 int cache_depth;size_t cache_limit;bool endpoint_pruning;
 std::unordered_map<TwoBits,uint64_t,TwoHash> memo;
 std::chrono::steady_clock::time_point start;double seconds=0;
 uint64_t dfs(int i,int vp,int wp){
  ++nodes;
  if((nodes&0xffff)==0&&seconds>0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=seconds){timeout=true;return 0;}
  int a=vp/Q,b=vp%Q;
  if(i==L){
   ++terminal_calls;uint64_t result=0;unsigned choices=(edges[a]>>(Q*wp))&((1u<<Q)-1);
   while(choices){int y=std::countr_zero(choices);choices&=choices-1;unsigned bit=1u<<(Q*wp+y);edges[a]^=bit;int next=Q*(wp%Q)+y;result+=std::popcount((edges[b]>>(Q*next))&((1u<<Q)-1));edges[a]|=bit;}
   return result;
  }
  unsigned choices=(edges[top[i]]>>(Q*vp))&((1u<<Q)-1);
  unsigned palette=0;for(int c=0;c<Q;++c)if(quota[c]>0)palette|=1u<<c;
  choices&=palette;
  if(endpoint_pruning){if(i==L-2)choices&=end_first;if(i==L-1)choices&=end_second[b];}
  if(!choices)return 0;
  TwoBits key=0;bool cached=cache_limit&&2*(L-i)+2<=cache_depth;
  if(cached){
   unsigned suffix=0;for(int j=i;j<L;++j)suffix=Q*suffix+top[j];
   key=TwoBits(edges[0])|(TwoBits(edges[1])<<T)|(TwoBits(edges[2])<<(2*T))|(TwoBits(vp*PAIRS+wp)<<81)|(TwoBits(suffix)<<88);
   ++lookups;auto it=memo.find(key);if(it!=memo.end()){++hits;return it->second;}
  }
  uint64_t result=0;
  while(choices){int x=std::countr_zero(choices);choices&=choices-1;unsigned upper=1u<<(Q*vp+x);edges[top[i]]^=upper;--quota[x];
   unsigned lower_choices=(edges[a]>>(Q*wp))&((1u<<Q)-1);
   while(lower_choices){int y=std::countr_zero(lower_choices);lower_choices&=lower_choices-1;unsigned lower=1u<<(Q*wp+y);edges[a]^=lower;
    result+=dfs(i+1,Q*b+x,Q*(wp%Q)+y);edges[a]|=lower;if(timeout)break;
   }
   ++quota[x];edges[top[i]]|=upper;if(timeout)return result;
  }
  if(cached&&memo.size()<cache_limit)memo.emplace(key,result);
  return result;
 }
public:
 uint64_t requests=0,nodes=0,terminal_calls=0,lookups=0,hits=0,initial_pairs=0;bool timeout=false;
 TwoRows(int depth=0,size_t capacity=0,bool endpoints=true):cache_depth(depth),cache_limit(capacity),endpoint_pruning(endpoints){if(depth<0||depth>32)throw std::invalid_argument("invalid memo depth");}
 uint64_t count(const int* fixed_top,const std::array<unsigned,3>&available,double budget=0){
  ++requests;start=std::chrono::steady_clock::now();seconds=budget;timeout=false;edges=available;
  for(int i=0;i<L;++i){top[i]=fixed_top[i];if(top[i]<0||top[i]>=Q)throw std::invalid_argument("invalid top color");}
  int n=0;std::array<int,Q> target{};std::array<int,PAIRS> degree{};
  for(int c=0;c<Q;++c){target[c]=std::popcount(edges[c]);n+=target[c];unsigned bits=edges[c];while(bits){int triple=std::countr_zero(bits);bits&=bits-1;++degree[triple/Q];--degree[triple%PAIRS];}}
  if(n!=2*L+2)throw std::invalid_argument("wrong residual edge count");
  for(int c:top)--target[c];
  for(int c:target)if(c<0)return 0;
  int positive=0;for(int d:degree)positive+=d>0?d:0;if(positive>2)return 0;
  uint64_t result=0;
  for(int vp=0;vp<PAIRS;++vp){quota=target;if(--quota[vp/Q]<0)continue;if(--quota[vp%Q]<0)continue;
   for(int wp=0;wp<PAIRS;++wp){
    bool okay=true;end_first=0;end_second.fill(0);
    for(int pair=0;pair<PAIRS;++pair){int ends=(pair==vp)+(pair==wp)-degree[pair];if(ends<0){okay=false;break;}if(ends){end_first|=1u<<(pair/Q);end_second[pair/Q]|=1u<<(pair%Q);}}
    if(!okay)continue;
    ++initial_pairs;result+=dfs(0,vp,wp);if(timeout)return result;
   }
  }
  return result;
 }
 size_t entries()const{return memo.size();}
};

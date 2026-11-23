#pragma once
// Exact prescribed-label Euler-trail counts, with reusable suffix states.
#include <array>
#include <bit>
#include <cstdint>
#include <stdexcept>
#include <unordered_map>
using LastBits=__uint128_t;
struct LastHash {size_t operator()(LastBits key)const{uint64_t a=key,b=key>>64;a^=b+0x9e3779b97f4a7c15ULL+(a<<6)+(a>>2);a^=a>>30;a*=0xbf58476d1ce4e5b9ULL;a^=a>>27;a*=0x94d049bb133111ebULL;return a^(a>>31);}};
class LastRow {
 int q,triples,cache_depth;size_t cache_limit;
 const int* top=nullptr;int length=0;
 std::unordered_map<LastBits,uint64_t,LastHash> memo;
 uint64_t visit(std::array<unsigned,3> edges,int i,int pair){
  while(true){
   ++calls[length-i];
   if(i==length)return 1;
   unsigned choices=(edges[top[i]]>>(q*pair))&((1u<<q)-1);
   if(!choices)return 0;
   if((choices&(choices-1))==0){int color=std::countr_zero(choices);edges[top[i]]^=1u<<(q*pair+color);pair=q*(pair%q)+color;++i;continue;}
   break;
  }
  LastBits key=0;bool cached=cache_limit&&length-i<=cache_depth;
  if(cached){
   unsigned suffix=0;for(int j=i;j<length;++j)suffix=q*suffix+top[j];
   key=LastBits(edges[0])|(LastBits(edges[1])<<triples)|(LastBits(edges[2])<<(2*triples))|(LastBits(suffix)<<81)|(LastBits(pair)<<108);
   ++lookups[length-i];auto it=memo.find(key);if(it!=memo.end()){++hits[length-i];return it->second;}
  }
  uint64_t total=0;unsigned choices=(edges[top[i]]>>(q*pair))&((1u<<q)-1);
  while(choices){int color=std::countr_zero(choices);choices&=choices-1;auto next=edges;next[top[i]]^=1u<<(q*pair+color);total+=visit(next,i+1,q*(pair%q)+color);}
  if(cached&&memo.size()<cache_limit)memo.emplace(key,total);
  return total;
 }
public:
 std::array<uint64_t,18> calls{},lookups{},hits{};
 uint64_t requests=0;
 LastRow(int colors,int depth=0,size_t capacity=0):q(colors),triples(q*q*q),cache_depth(depth),cache_limit(capacity){if(q<2||q>3||depth<0||depth>17)throw std::invalid_argument("last-row dimensions");}
 uint64_t count(const int* prescribed,int size,const std::array<unsigned,3>&edges,unsigned starts){
  if(size<0||size>17)throw std::invalid_argument("last-row length");
  int n=0;for(int color=0;color<q;++color)n+=std::popcount(edges[color]);
  if(n!=size)throw std::invalid_argument("edge count differs from top word length");
  top=prescribed;length=size;++requests;uint64_t total=0;
  for(int pair=0;pair<q*q;++pair)if(starts>>pair&1)total+=visit(edges,0,pair);
  return total;
 }
 size_t entries()const{return memo.size();}
};

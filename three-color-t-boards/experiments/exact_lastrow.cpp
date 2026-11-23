// Read (q^2)^2-digit prefixes, one per line, and count their final rows.
#include "exact_lastrow.hpp"
#include <iostream>
#include <string>
int main(int argc,char**argv){try{
 int q=argc>1?std::stoi(argv[1]):3,depth=argc>2?std::stoi(argv[2]):8;
 size_t capacity=argc>3?std::stoull(argv[3]):1000000;
 LastRow counter(q,depth,capacity);std::string prefix;int h=q*q+1,triple_count=q*q*q;
 while(std::cin>>prefix){if(prefix.size()!=size_t((h-1)*(h-1)))throw std::invalid_argument("wrong prefix length");for(char c:prefix)if(c<'0'||c>='0'+q)throw std::invalid_argument("bad color");
  std::array<unsigned,3> edges{};for(int c=0;c<q;++c)edges[c]=(1u<<triple_count)-1;
  bool valid=true;
  for(int r=1;r<h-1;++r)for(int j=0;j<2*r-1;++j){int t=prefix[(r-1)*(r-1)+j]-'0',code=(prefix[r*r+j]-'0')*q*q+(prefix[r*r+j+1]-'0')*q+prefix[r*r+j+2]-'0';unsigned bit=1u<<code;if(!(edges[t]&bit))valid=false;edges[t]&=~bit;}
  std::array<int,17> top{};int length=2*h-3;for(int j=0;j<length;++j)top[j]=prefix[(h-2)*(h-2)+j]-'0';
  std::cout<<(valid?counter.count(top.data(),length,edges,(1u<<(q*q))-1):0)<<'\n';
 }
 std::cerr<<"requests="<<counter.requests<<" entries="<<counter.entries()<<'\n';
 for(int d=0;d<=17;++d)if(counter.calls[d])std::cerr<<"remaining="<<d<<" calls="<<counter.calls[d]<<" lookups="<<counter.lookups[d]<<" hits="<<counter.hits[d]<<'\n';
 }catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}}

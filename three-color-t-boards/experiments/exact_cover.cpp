// Colored exact cover for all ordered-T patterns. No external solver.
// Candidate (position, pattern) covers those two primary columns and assigns
// colors to the four cells. Inconsistent cell assignments are pairwise conflicts.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#include "exact_cover_hall.hpp"
using U128=__uint128_t;
constexpr int MAXW=103, MAXC=162;
struct State {
 std::array<uint64_t,MAXW> active{};
 std::array<uint16_t,MAXC> count{};
 std::array<uint64_t,3> covered{};
 std::array<uint8_t,100> domains{};
 int left=0;bool isolated=false;
};
struct Hash {size_t operator()(const std::vector<uint64_t>&v)const{uint64_t h=0x243f6a8885a308d3ULL;for(auto x:v){x^=x>>30;x*=0xbf58476d1ce4e5b9ULL;x^=x>>27;x*=0x94d049bb133111ebULL;x^=x>>31;h^=x+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}return h;}};
std::string decimal(U128 x){std::string s;do{s.push_back('0'+x%10);x/=10;}while(x);std::reverse(s.begin(),s.end());return s;}
U128 add_count(U128 a,U128 b){if(~U128(0)-a<b)throw std::overflow_error("128-bit count overflow");return a+b;}
U128 multiply_count(U128 a,U128 b){if(b&&a>~U128(0)/b)throw std::overflow_error("128-bit count overflow");return a*b;}
class Solver {
 int q,h,n,ncells,nrows,nwords,ncols,mode;
 std::vector<std::array<int,4>> windows,digits;
 std::vector<std::vector<uint64_t>> cover,conflict,supports;
 std::array<std::vector<int>,4> role_cells;
 std::vector<int> pos,pat;
 std::unordered_map<std::vector<uint64_t>,U128,Hash> memo;
 size_t memo_limit;double seconds;bool propagate_cells,branch_cells,hall_prune,flow,components;int hall_limit;
 std::chrono::steady_clock::time_point started;
public:
 uint64_t nodes=0,forced=0,hits=0,dead=0,solutions_seen=0,cell_prunes=0,hall_calls=0,hall_failed=0,hall_removed=0,cell_branches=0,flow_failed=0,flow_removed=0,component_splits=0,component_max=0;bool timeout=false;
 Solver(int colors,int strategy,size_t cache,double time,bool propagation,bool branching,int hall,bool pruning,bool flows,bool decomposition):q(colors),h(q*q+1),n(q*q*q*q),ncells(h*h),nrows(n*n),nwords((nrows+63)/64),ncols(2*n),mode(strategy),memo_limit(cache),seconds(time),propagate_cells(propagation),branch_cells(branching),hall_prune(pruning),flow(flows),components(decomposition),hall_limit(hall){
  for(int r=1;r<h;++r)for(int j=0;j<2*r-1;++j)windows.push_back({(r-1)*(r-1)+j,r*r+j,r*r+j+1,r*r+j+2});
  for(const auto &w:windows)for(int role=0;role<4;++role)role_cells[role].push_back(w[role]);
  for(int p=0;p<n;++p){int v=p;std::array<int,4>d{};for(int k=3;k>=0;--k){d[k]=v%q;v/=q;}digits.push_back(d);}
  cover.assign(ncols,std::vector<uint64_t>(nwords));
  supports.assign(ncells*q,std::vector<uint64_t>(nwords));
  pos.resize(nrows);pat.resize(nrows);
  for(int r=0;r<nrows;++r){int w=r/n,p=r%n;pos[r]=w;pat[r]=n+p;uint64_t bit=uint64_t(1)<<(r%64);cover[w][r/64]|=bit;cover[n+p][r/64]|=bit;
   for(int k=0;k<4;++k)supports[q*windows[w][k]+digits[p][k]][r/64]|=bit;
  }
  conflict.assign(nrows,std::vector<uint64_t>(nwords));
  for(int r=0;r<nrows;++r){int w=r/n,p=r%n;for(int k=0;k<nwords;++k)conflict[r][k]=cover[w][k]|cover[n+p][k];
   for(int k=0;k<4;++k)for(int c=0;c<q;++c)if(c!=digits[p][k])for(int b=0;b<nwords;++b)conflict[r][b]|=supports[q*windows[w][k]+c][b];
  }
 }
 bool covered(const State&s,int col)const{return (s.covered[col/64]>>(col%64))&1;}
 template<typename Mask> void remove(State&s,const Mask&mask){
  for(int b=0;b<nwords;++b){uint64_t gone=s.active[b]&mask[b];s.active[b]&=~gone;
   while(gone){int r=64*b+std::countr_zero(gone);gone&=gone-1;--s.count[pos[r]];--s.count[pat[r]];}
  }
 }
 void choose(State&s,int row){
  int c1=pos[row],c2=pat[row];s.covered[c1/64]|=uint64_t(1)<<(c1%64);s.covered[c2/64]|=uint64_t(1)<<(c2%64);--s.left;
  for(int k=0;k<4;++k)s.domains[windows[c1][k]]=1<<digits[c2-n][k];
  remove(s,conflict[row]);
 }
 bool cell_consistency(State&s){
  bool changed;
  do{
   changed=false;std::array<uint64_t,MAXW> kill{};
   auto restrict=[&](int cell,unsigned domain){
    unsigned removed=s.domains[cell]&~domain;
    if(removed){changed=true;s.domains[cell]=domain;++cell_prunes;
     for(int color=0;color<q;++color)if(removed>>color&1)for(int b=0;b<nwords;++b)kill[b]|=supports[cell*q+color][b];}
   };
   for(int w=0;w<n;++w)if(!covered(s,w)){
    if(!s.count[w])return false;
    int first=w*n/64,last=((w+1)*n-1)/64;
    for(int k=0;k<4;++k){int cell=windows[w][k];unsigned allowed=0;
     for(int color=0;color<q;++color)if(s.domains[cell]>>color&1){
      for(int b=first;b<=last;++b)if(s.active[b]&cover[w][b]&supports[cell*q+color][b]){allowed|=1u<<color;break;}
     }
     if(!allowed)return false;
     restrict(cell,allowed);
    }
   }
   // Every color occurs q^3 times in each of the four T roles.
   if(!s.isolated)for(int role=0;role<4;++role)for(int color=0;color<q;++color){
    unsigned bit=1u<<color;int possible=0,fixed=0;
    for(int cell:role_cells[role]){possible+=bool(s.domains[cell]&bit);fixed+=s.domains[cell]==bit;}
    if(possible<q*q*q||fixed>q*q*q)return false;
    if(fixed==q*q*q||possible==q*q*q)for(int cell:role_cells[role])if(s.domains[cell]&bit){
     unsigned next=s.domains[cell];
     if(possible==q*q*q)next=bit;else if(next!=bit)next&=~bit;
     if(!next)return false;
     restrict(cell,next);
    }
   }
   if(changed)remove(s,kill);
  }while(changed);
  return true;
 }
 int flow_consistency(State&s){
  std::array<std::array<unsigned,9>,2> endpoint{};
  for(int side=0;side<2;++side)for(int r=1;r<h;++r){
   int w=side?r*r-1:(r-1)*(r-1),role=side?2:1;
   if(covered(s,w)){
    int a=std::countr_zero(unsigned(s.domains[windows[w][role]])),b=std::countr_zero(unsigned(s.domains[windows[w][role+1]]));
    endpoint[side][r-1]=1u<<(q*a+b);
   }else for(int b=w*n/64;b<=((w+1)*n-1)/64;++b){uint64_t bits=s.active[b]&cover[w][b];while(bits){int row=64*b+std::countr_zero(bits);bits&=bits-1;int p=pat[row]-n;endpoint[side][r-1]|=1u<<(q*digits[p][role]+digits[p][role+1]);}}
   if(!endpoint[side][r-1])return -1;
  }
  bool changed;
  do{
   changed=false;
   for(int pair=0;pair<q*q;++pair){unsigned bit=1u<<pair;int possible[2]{},fixed[2]{};
    for(int side=0;side<2;++side)for(int r=0;r<h-1;++r){possible[side]+=bool(endpoint[side][r]&bit);fixed[side]+=endpoint[side][r]==bit;}
    if(fixed[0]>possible[1]||fixed[1]>possible[0]){++flow_failed;return -1;}
    for(int side=0;side<2;++side)if(fixed[side]==possible[1-side]){
     for(int r=0;r<h-1;++r){
      unsigned &same=endpoint[side][r],&other=endpoint[1-side][r];
      if((same&bit)&&same!=bit){same&=~bit;changed=true;if(!same)return -1;}
      if((other&bit)&&other!=bit){other=bit;changed=true;}
     }
    }
   }
  }while(changed);
  std::array<uint64_t,MAXW> kill{};unsigned removed=0;
  for(int side=0;side<2;++side)for(int r=1;r<h;++r){int w=side?r*r-1:(r-1)*(r-1),role=side?2:1;if(covered(s,w))continue;
   for(int b=w*n/64;b<=((w+1)*n-1)/64;++b){uint64_t bits=s.active[b]&cover[w][b];while(bits){int row=64*b+std::countr_zero(bits);bits&=bits-1;int p=pat[row]-n,pair=q*digits[p][role]+digits[p][role+1];if(!(endpoint[side][r-1]>>pair&1))kill[row/64]|=uint64_t(1)<<(row%64);}}
  }
  for(int b=0;b<nwords;++b)removed+=std::popcount(kill[b]);
  if(!removed)return 0;
  flow_removed+=removed;remove(s,kill);return 1;
 }
 int hall_consistency(State&s){
  exact_hall::Domains domains{},supported{};U128 left=0,right=0;
  for(int p=0;p<n;++p)if(!covered(s,n+p))right|=U128(1)<<p;
  for(int w=0;w<n;++w)if(!covered(s,w)){
   left|=U128(1)<<w;
   for(int b=w*n/64;b<=((w+1)*n-1)/64;++b){uint64_t bits=s.active[b]&cover[w][b];while(bits){int r=64*b+std::countr_zero(bits);bits&=bits-1;domains[w]|=U128(1)<<(pat[r]-n);}}
  }
  ++hall_calls;auto result=exact_hall::filter(domains,left,right,supported,hall_prune);
  if(!result.feasible){++hall_failed;return -1;}
  if(!result.removed)return 0;
  hall_removed+=result.removed;std::array<uint64_t,MAXW> kill{};
  for(int w=0;w<n;++w){U128 bad=domains[w]&~supported[w];while(bad){int p=exact_hall::first(bad);bad&=bad-1;int r=w*n+p;kill[r/64]|=uint64_t(1)<<(r%64);}}
  remove(s,kill);return 1;
 }
 int best_cell(const State&s,int max_options)const{
  int chosen=-1,fewest=max_options,score=-1;
  std::array<int,100> pressure{};
  for(int w=0;w<n;++w)if(!covered(s,w))for(int cell:windows[w])pressure[cell]+=256/(1+s.count[w]);
  for(int cell=0;cell<ncells;++cell){int options=std::popcount(unsigned(s.domains[cell]));
   if(!pressure[cell])continue;
   if(options>1&&(options<fewest||(options==fewest&&chosen>=0&&pressure[cell]>score))){chosen=cell;fewest=options;score=pressure[cell];}
  }
  return chosen;
 }
 std::vector<U128> groups(const State&s)const{
  std::array<int,81> parent,pattern_owner;std::array<int,100> cell_owner;
  for(int i=0;i<n;++i)parent[i]=i;
  pattern_owner.fill(-1);cell_owner.fill(-1);
  auto root=[&](int i){while(parent[i]!=i){parent[i]=parent[parent[i]];i=parent[i];}return i;};
  auto join=[&](int i,int j){i=root(i);j=root(j);if(i!=j)parent[j]=i;};
  for(int w=0;w<n;++w)if(!covered(s,w))for(int cell:windows[w])if(std::popcount(unsigned(s.domains[cell]))>1){
   if(cell_owner[cell]>=0)join(w,cell_owner[cell]);else cell_owner[cell]=w;
  }
  for(int b=0;b<nwords;++b){uint64_t bits=s.active[b];while(bits){int row=64*b+std::countr_zero(bits);bits&=bits-1;int w=pos[row],p=pat[row]-n;
   if(pattern_owner[p]>=0)join(w,pattern_owner[p]);else pattern_owner[p]=w;
  }}
  std::array<U128,81> masks{};
  for(int w=0;w<n;++w)if(!covered(s,w))masks[root(w)]|=U128(1)<<w;
  std::vector<U128> result;for(int w=0;w<n;++w)if(masks[w])result.push_back(masks[w]);
  return result;
 }
 State isolate(const State&s,U128 members)const{
  State child=s;child.isolated=true;child.left=exact_hall::population(members);child.active.fill(0);child.count.fill(0);child.covered.fill(~uint64_t(0));
  for(int b=0;b<nwords;++b){uint64_t bits=s.active[b];while(bits){int row=64*b+std::countr_zero(bits);bits&=bits-1;int w=pos[row],p=pat[row];if(members>>w&1){
   child.active[b]|=uint64_t(1)<<(row%64);++child.count[w];++child.count[p];child.covered[w/64]&=~(uint64_t(1)<<(w%64));child.covered[p/64]&=~(uint64_t(1)<<(p%64));
  }}}
  return child;
 }
 int best(const State&s)const{
  int result=-1,min=n+1;
  // A zero anywhere is fatal even when branching is restricted to one kind.
  for(int c=0;c<ncols;++c)if(!covered(s,c)){
   if(s.count[c]==0)return c;
   if(mode==1&&c>=n)continue;
   if(mode==2&&c<n)continue;
   if(s.count[c]<min){min=s.count[c];result=c;}
  }
  return result;
 }
 U128 dfs(State s){
  if((++nodes&1023)==0&&seconds>0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()>=seconds){timeout=true;return 0;}
  int c;
  while(true){
   if(!s.left){++solutions_seen;return 1;}
   if(propagate_cells&&!cell_consistency(s)){++dead;return 0;}
   if(flow&&!s.isolated){int result=flow_consistency(s);if(result<0){++dead;return 0;}if(result>0)continue;}
   c=best(s);if(c<0)throw std::runtime_error("no primary column");
   if(!s.count[c]){++dead;return 0;}
   if(s.count[c]!=1){
    if(hall_limit&&s.left<=hall_limit){int result=hall_consistency(s);if(result<0){++dead;return 0;}if(result>0)continue;}
    break;
   }
   int r=-1;for(int b=0;b<nwords;++b)if(uint64_t bits=s.active[b]&cover[c][b]){r=64*b+std::countr_zero(bits);break;}
   if(r<0)throw std::runtime_error("bad column count");
   choose(s,r);++forced;
  }
  std::vector<uint64_t> key;
  if(memo_limit){key.assign(s.active.begin(),s.active.begin()+nwords);auto it=memo.find(key);if(it!=memo.end()){++hits;return it->second;}}
  if(components){auto parts=groups(s);if(parts.size()>1){
   ++component_splits;component_max=std::max(component_max,uint64_t(parts.size()));U128 product=1;
   for(U128 members:parts){State child=isolate(s,members);int patterns=0;for(int p=n;p<ncols;++p)patterns+=!covered(child,p);if(patterns!=child.left)return 0;
    product=multiply_count(product,dfs(child));if(timeout)return 0;if(!product)break;
   }
   if(memo.size()<memo_limit)memo.emplace(std::move(key),product);
   return product;
  }}
  U128 result=0;
  int cell=branch_cells?best_cell(s,s.count[c]):-1;
  if(cell>=0){
   ++cell_branches;
   for(int color=0;color<q;++color)if(s.domains[cell]>>color&1){State next=s;next.domains[cell]=1u<<color;std::array<uint64_t,MAXW> kill{};
    for(int other=0;other<q;++other)if(other!=color)for(int b=0;b<nwords;++b)kill[b]|=supports[cell*q+other][b];
    remove(next,kill);result=add_count(result,dfs(next));if(timeout)return result;
   }
  }else for(int b=0;b<nwords;++b){uint64_t options=s.active[b]&cover[c][b];while(options){int r=64*b+std::countr_zero(options);options&=options-1;State next=s;choose(next,r);result=add_count(result,dfs(next));if(timeout)return result;}}
  if(memo.size()<memo_limit)memo.emplace(std::move(key),result);
  return result;
 }
 U128 run(const std::string&prefix,const std::string&support_file){
  if(prefix.size()>size_t(ncells))throw std::runtime_error("prefix too long");
  for(char c:prefix)if(c<'0'||c>='0'+q)throw std::runtime_error("invalid prefix color");
  State s;s.left=n;s.domains.fill((1u<<q)-1);
  for(size_t cell=0;cell<prefix.size();++cell)s.domains[cell]=1u<<(prefix[cell]-'0');
  std::array<U128,81> allowed{};
  if(!support_file.empty()){
   std::ifstream file(support_file);if(!file)throw std::runtime_error("could not read supports file");
   std::string board;size_t inputs=0;
   while(file>>board){if(board.size()!=size_t(ncells))throw std::runtime_error("support board has wrong size");for(char c:board)if(c<'0'||c>='0'+q)throw std::runtime_error("invalid support board color");
    for(int w=0;w<n;++w){int pattern=0;for(int cell:windows[w])pattern=q*pattern+board[cell]-'0';allowed[w]|=U128(1)<<pattern;}++inputs;
   }
   if(!inputs)throw std::runtime_error("empty supports file");
  }
  for(int r=0;r<nrows;++r){bool okay=true;int w=r/n,p=r%n;
   if(!support_file.empty()&&!(allowed[w]>>p&1))continue;
   for(int k=0;k<4;++k)if(windows[w][k]<int(prefix.size())&&digits[p][k]!=prefix[windows[w][k]]-'0'){okay=false;break;}
   if(okay){s.active[r/64]|=uint64_t(1)<<(r%64);++s.count[pos[r]];++s.count[pat[r]];}
  }
  started=std::chrono::steady_clock::now();return dfs(s);
 }
 double elapsed()const{return std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();}
 size_t cached()const{return memo.size();}
};
int main(int argc,char**argv){try{
 int q=3,mode=0;size_t cache=0;double seconds=30;std::string prefix,support_file;bool cells=false,branching=false,hall_prune=true,flow=false,components=false;int hall=0;
 for(int i=1;i<argc;i+=2){if(i+1==argc)throw std::runtime_error("option needs value");std::string k=argv[i],v=argv[i+1];
  if(k=="--colors")q=std::stoi(v);else if(k=="--prefix")prefix=v;else if(k=="--seconds")seconds=std::stod(v);else if(k=="--memo")cache=std::stoull(v);
  else if(k=="--cells")cells=std::stoi(v)!=0;
  else if(k=="--branch-cells")branching=std::stoi(v)!=0;
  else if(k=="--hall")hall=std::stoi(v);
  else if(k=="--hall-prune")hall_prune=std::stoi(v)!=0;
  else if(k=="--flow")flow=std::stoi(v)!=0;
  else if(k=="--components")components=std::stoi(v)!=0;
  else if(k=="--supports-file")support_file=v;
  else if(k=="--mode"){if(v=="hybrid")mode=0;else if(v=="position")mode=1;else if(v=="pattern")mode=2;else throw std::runtime_error("bad mode");}
  else throw std::runtime_error("unknown option");
 }
 if(q<2||q>3||seconds<0||!std::isfinite(seconds)||hall<0||hall>81)throw std::runtime_error("bad dimensions, Hall threshold, or time");
 Solver s(q,mode,cache,seconds,cells||branching,branching,hall,hall_prune,flow,components);U128 result=s.run(prefix,support_file);
 std::cout<<"status="<<(s.timeout?"INCOMPLETE":"COMPLETE")<<" colors="<<q<<" prefix="<<prefix<<" mode="<<mode
 <<" count="<<decimal(result)<<" nodes="<<s.nodes<<" forced="<<s.forced<<" dead="<<s.dead<<" memo_entries="<<s.cached()<<" memo_hits="<<s.hits<<" cell_prunes="<<s.cell_prunes<<" hall_calls="<<s.hall_calls<<" hall_failed="<<s.hall_failed<<" hall_removed="<<s.hall_removed<<" cell_branches="<<s.cell_branches<<" flow_failed="<<s.flow_failed<<" flow_removed="<<s.flow_removed<<" component_splits="<<s.component_splits<<" component_max="<<s.component_max<<" elapsed="<<s.elapsed()<<"\n";
 return s.timeout?1:0;
 }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 2;}}

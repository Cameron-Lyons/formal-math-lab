// Exact bottom-up diagonal T-board counter. Each nonbottom cell completes
// the T consisting of itself and its three children, all already assigned.
#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using Count=__uint128_t;
std::string decimal(Count n){std::string s;do{s.push_back('0'+n%10);n/=10;}while(n);std::reverse(s.begin(),s.end());return s;}
struct Cell {int id,child,roles;bool fixed;std::array<int,2> events{};int event_count=0;};
struct Pair {int left,right,sign;};
class Search {
 int q,h,limit;double seconds;bool reverse,flow;
 std::array<int,100> value{},role{},child{};
 std::array<bool,100> fixed{},seeded{};
 std::array<std::array<int,3>,4> counts{};
 std::array<unsigned,4> allowed{};
 std::array<unsigned,27> available{};
 std::vector<Cell> order;
 std::vector<Pair> pairs;
 std::array<int,9> balance{};
 int excess=0,remaining_ends=0;
 std::chrono::steady_clock::time_point start;
public:
 uint64_t nodes=0,flow_prunes=0;Count count=0;bool timeout=false,impossible=false;
 Search(int colors,double time,bool reflected,bool use_flow,std::string prefix,std::string mask):q(colors),h(q*q+1),limit(q*q*q),seconds(time),reverse(reflected),flow(use_flow){
  value.fill(-1);child.fill(-1);allowed.fill((1u<<q)-1);available.fill((1u<<q)-1);
  if(prefix.size()>size_t(h*h)||mask.size()>size_t(h*h))throw std::runtime_error("fixed data too long");
  for(size_t i=0;i<prefix.size();++i){char c=prefix[i];if(c<'0'||c>='0'+q)throw std::runtime_error("bad prefix color");value[i]=c-'0';fixed[i]=true;}
  for(size_t i=0;i<mask.size();++i){char c=mask[i];if(c=='.')continue;if(c<'0'||c>='0'+q)throw std::runtime_error("bad fixed color");if(fixed[i]&&value[i]!=c-'0')throw std::runtime_error("conflicting fixed values");value[i]=c-'0';fixed[i]=true;}
  for(int r=1;r<h;++r)for(int j=0;j<2*r-1;++j){int cells[4]={(r-1)*(r-1)+j,r*r+j,r*r+j+1,r*r+j+2};child[cells[0]]=cells[1];for(int k=0;k<4;++k)role[cells[k]]|=1<<k;}
  for(int i=0;i<h*h;++i)if(fixed[i])for(int k=0;k<4;++k)if(role[i]>>k&1){if(++counts[k][value[i]]>limit)impossible=true;}
  for(int k=0;k<4;++k)for(int c=0;c<q;++c)if(counts[k][c]>=limit)allowed[k]&=~(1u<<c);
  for(int i=0;i<h*h;++i)if(child[i]>=0&&fixed[i]&&fixed[child[i]]&&fixed[child[i]+1]&&fixed[child[i]+2]){
   int triple=(value[child[i]]*q+value[child[i]+1])*q+value[child[i]+2];unsigned bit=1u<<value[i];if(!(available[triple]&bit))impossible=true;available[triple]&=~bit;seeded[i]=true;
  }
  std::array<bool,100> visited=fixed;
  for(int diagonal=0;diagonal<2*h-1;++diagonal)for(int r=h-1;r>=0;--r){int col=diagonal-2*(h-1-r);if(col<0)break;if(reverse)col=2*r-col;int i=r*r+col;
   if(child[i]>=0)for(int j=0;j<3;++j)if(!visited[child[i]+j])throw std::runtime_error("invalid diagonal schedule");
   visited[i]=true;if(fixed[i]&&(child[i]<0||seeded[i]))continue;order.push_back({i,child[i],role[i],fixed[i]});
  }
  for(int i=0;i<h*h;++i)if(!visited[i])throw std::runtime_error("schedule missed cell");
  if(flow){
   std::array<int,100> when;when.fill(-1);for(size_t k=0;k<order.size();++k)if(!order[k].fixed)when[order[k].id]=k;
   for(int r=1;r<h;++r)for(int side=0;side<2;++side){
    Pair p{r*r+(side?2*r-1:0),r*r+(side?2*r:1),side?-1:1};
    int last=std::max(when[p.left],when[p.right]);
    if(last<0)balance[q*value[p.left]+value[p.right]]+=p.sign;
    else {if(side)++remaining_ends;if(order[last].event_count>=2)throw std::logic_error("too many endpoint events");order[last].events[order[last].event_count++]=pairs.size();pairs.push_back(p);}
   }
   for(int b:balance)excess+=std::max(b,0);
   if(excess>remaining_ends)impossible=true;
  }
 }
 void endpoint(int id,int direction){const Pair&p=pairs[id];int &b=balance[q*value[p.left]+value[p.right]],delta=p.sign*direction;excess+=std::max(b+delta,0)-std::max(b,0);b+=delta;if(p.sign<0)remaining_ends-=direction;}
 void dfs(size_t p){
  if((++nodes&0xfffff)==0&&seconds>0&&std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>=seconds){timeout=true;return;}
  if(p==order.size()){if(count==~Count(0))throw std::overflow_error("count overflow");++count;return;}
  const Cell &cell=order[p];int triple=-1;unsigned choices=(1u<<q)-1;
  if(cell.child>=0){triple=(value[cell.child]*q+value[cell.child+1])*q+value[cell.child+2];choices=available[triple];}
  if(cell.fixed)choices&=1u<<value[cell.id];
  else for(int k=0;k<4;++k)if(cell.roles>>k&1)choices&=allowed[k];
  while(choices){int color=std::countr_zero(choices);unsigned bit=1u<<color;choices&=choices-1;
   if(!cell.fixed){value[cell.id]=color;for(int k=0;k<4;++k)if(cell.roles>>k&1){if(++counts[k][color]==limit)allowed[k]&=~bit;}}
   if(triple>=0)available[triple]^=bit;
   if(flow)for(int k=0;k<cell.event_count;++k)endpoint(cell.events[k],1);
   if(!flow||excess<=remaining_ends)dfs(p+1);else ++flow_prunes;
   if(flow)for(int k=cell.event_count-1;k>=0;--k)endpoint(cell.events[k],-1);
   if(triple>=0)available[triple]|=bit;
   if(!cell.fixed)for(int k=0;k<4;++k)if(cell.roles>>k&1){--counts[k][color];allowed[k]|=bit;}
   if(timeout)return;
  }
 }
 void run(){start=std::chrono::steady_clock::now();if(!impossible)dfs(0);}
 double elapsed()const{return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
 size_t open_steps()const{return order.size();}
};
int main(int argc,char**argv){try{
 int q=3;double seconds=15;bool reverse=false,normalize=false,flow=false;std::string prefix,mask;
 for(int i=1;i<argc;i+=2){if(i+1==argc)throw std::runtime_error("missing option value");std::string k=argv[i],v=argv[i+1];
  if(k=="--colors")q=std::stoi(v);else if(k=="--seconds")seconds=std::stod(v);else if(k=="--prefix")prefix=v;else if(k=="--fixed")mask=v;else if(k=="--reverse")reverse=std::stoi(v)!=0;else if(k=="--normalize-apex")normalize=std::stoi(v)!=0;else if(k=="--flow")flow=std::stoi(v)!=0;else throw std::runtime_error("unknown option");
 }
 if(q<2||q>3||seconds<0||!std::isfinite(seconds))throw std::runtime_error("bad colors or time");
 if(normalize){if(!prefix.empty()||!mask.empty())throw std::runtime_error("apex normalization requires otherwise unrestricted region");prefix="0";}
 Search s(q,seconds,reverse,flow,prefix,mask);s.run();
 std::cout<<"status="<<(s.timeout?"INCOMPLETE":"COMPLETE")<<" colors="<<q<<" reverse="<<reverse<<" prefix="<<prefix<<" fixed="<<mask<<" flow="<<flow<<" steps="<<s.open_steps()<<" nodes="<<s.nodes<<" flow_prunes="<<s.flow_prunes;
 if(s.timeout)std::cout<<" completed_leaves="<<decimal(s.count);
 else {std::cout<<" exact_count="<<decimal(s.count);if(normalize){if(s.count>~Count(0)/q)throw std::overflow_error("normalized count overflow");std::cout<<" unrestricted_labeled_count="<<decimal(s.count*q);}}
 std::cout<<" elapsed="<<s.elapsed()<<"\n";return s.timeout?1:0;
 }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 2;}}

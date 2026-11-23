// Bounded, exact DFS within a supplied prefix. Every reported leaf is a witness.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
using namespace std;
using Bits = unsigned __int128;
int values[100], windowtop[100], roles[100], counts[4][3];
unsigned long long nodes=0, leaves=0, fresh=0, max_new=0;
chrono::steady_clock::time_point started, deadline;
bool timeout_hit=false, count_limit_hit=false;
unordered_set<string> known;
ofstream output;

string canonical(const string &a) {
 string best(100,'3');array<int,3> p={0,1,2};
 do {
  string s=a;for(char &c:s)c='0'+p[c-'0'];best=min(best,s);
  for(int r=0;r<10;r++)reverse(s.begin()+r*r,s.begin()+(r+1)*(r+1));
  best=min(best,s);
 }while(next_permutation(p.begin(),p.end()));
 return best;
}

void dfs(int pos,Bits used) {
 if((++nodes&0xfffff)==0 && chrono::steady_clock::now()>deadline){timeout_hit=true;return;}
 if(pos==100){
  ++leaves;string s;for(int c:values)s.push_back('0'+c);
  if(!known.insert(canonical(s)).second)return;
  ++fresh;output<<"{\"rows\":[";
  for(int r=0;r<10;r++){if(r)output<<',';output<<'"'<<s.substr(r*r,2*r+1)<<'"';}
  output<<"],\"nodes\":"<<nodes<<",\"leaves\":"<<leaves<<"}"<<endl;
  cerr<<"new orbit "<<fresh<<" nodes "<<nodes<<" elapsed "<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
  if(max_new && fresh>=max_new)count_limit_hit=true;
  return;
 }
 int base=windowtop[pos]>=0?27*values[windowtop[pos]]+9*values[pos-2]+3*values[pos-1]:0;
 int mask=roles[pos];
 for(int c=0;c<3;c++){
  bool capped=false;for(int k=0;k<4;k++)if((mask&(1<<k))&&counts[k][c]>=27){capped=true;break;}
  if(capped)continue;
  Bits bit=windowtop[pos]>=0?(Bits(1)<<(base+c)):0;
  if(used&bit)continue;
  values[pos]=c;
  for(int k=0;k<4;k++)if(mask&(1<<k))++counts[k][c];
  dfs(pos+1,used|bit);
  for(int k=0;k<4;k++)if(mask&(1<<k))--counts[k][c];
  if(timeout_hit || count_limit_hit)return;
 }
}

int main(int argc,char**argv){
 if(argc!=6 && argc!=7){cerr<<"usage: more_search FLAT_PREFIX ROWS SECONDS KNOWN_FLATS OUTPUT_JSONL [MAX_NEW]\n";return 2;}
 if(argc==7){max_new=stoull(argv[6]);if(!max_new){cerr<<"MAX_NEW must be positive\n";return 2;}}
 int row_count=stoi(argv[2]),seconds=stoi(argv[3]);
 if(row_count<0 || row_count>10 || seconds<=0){cerr<<"ROWS must be 0..10; SECONDS must be positive\n";return 2;}
 fill(windowtop,windowtop+100,-1);
 for(int r=1;r<10;r++)for(int j=0;j<2*r-1;j++){
  windowtop[r*r+j+2]=(r-1)*(r-1)+j;
  roles[(r-1)*(r-1)+j]|=1;
  roles[r*r+j]|=2;roles[r*r+j+1]|=4;roles[r*r+j+2]|=8;
 }
 ifstream file(argv[4]);if(!file){cerr<<"cannot read known boards\n";return 2;}
 string s;while(file>>s){
  if(s.size()!=100 || s.find_first_not_of("012")!=string::npos){cerr<<"malformed known board\n";return 2;}
  known.insert(canonical(s));
 }
 int plen=row_count*row_count;string prefix=argv[1];
 if((int)prefix.size()<plen)return 2;
 Bits used=0;
 for(int p=0;p<plen;p++){
  int c=prefix[p]-'0';if(c<0||c>2)return 2;values[p]=c;
  for(int k=0;k<4;k++)if(roles[p]&(1<<k))if(++counts[k][c]>27)return 2;
  if(windowtop[p]>=0){int code=27*values[windowtop[p]]+9*values[p-2]+3*values[p-1]+values[p];Bits bit=Bits(1)<<code;if(used&bit)return 2;used|=bit;}
 }
 output.open(argv[5],ios::app);
 if(!output){cerr<<"cannot open output\n";return 2;}
 started=chrono::steady_clock::now();deadline=started+chrono::seconds(seconds);
 dfs(plen,used);
 const char *status=timeout_hit?"timeout":(count_limit_hit?"count_limit":"complete");
 cerr<<"nodes="<<nodes<<" leaves="<<leaves<<" new_orbits="<<fresh<<" exhaustive="<<(!timeout_hit && !count_limit_hit)<<" elapsed="<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<" termination="<<status<<endl;
 return timeout_hit?1:0;
}

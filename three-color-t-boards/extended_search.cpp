// Enumerate a fixed upper-row fiber, recording new symmetry classes immediately.
// Independent implementation; colors 0,1,2 and T order top,left,middle,right.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
using namespace std;
__extension__ using Bits=unsigned __int128;
int v[100], counts[4][3], wtop[100], roleMask[100];
unsigned long long nodes=0, sols=0, fresh=0;
chrono::steady_clock::time_point started, deadline;
unordered_set<string> known;
bool timedout=false;
ofstream result;
string canonical(string s){
 auto normalize=[](string t){int map[3]={-1,-1,-1},next=0;for(char&c:t){int x=c-'0';if(map[x]<0)map[x]=next++;c='0'+map[x];}return t;};
 string ref=s;for(int r=0;r<10;r++)reverse(ref.begin()+r*r,ref.begin()+(r+1)*(r+1));
 return min(normalize(s),normalize(ref));
}
void record(){
 ++sols;string s;for(int c:v)s.push_back('0'+c);
 string key=canonical(s);if(!known.insert(key).second)return;
 ++fresh;result<<"{\"rows\":[";
 for(int r=0;r<10;r++){if(r)result<<",";result<<'"'<<s.substr(r*r,2*r+1)<<'"';}
 result<<"],\"nodes\":"<<nodes<<",\"solutions_seen\":"<<sols<<",\"elapsed\":"<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<"}"<<endl;
 cerr<<"NEW orbit "<<fresh<<" at node "<<nodes<<" total solutions "<<sols<<endl;
}
void visit(int p,Bits used){
 if((++nodes & 0xfffff)==0 && chrono::steady_clock::now()>deadline){timedout=true;return;}
 if(p==100){record();return;}
 int base=wtop[p]>=0?27*v[wtop[p]]+9*v[p-2]+3*v[p-1]:0;
 int roles=roleMask[p];
 for(int c=0;c<3;c++){
  bool over=false;for(int role=0;role<4;role++)if((roles>>role&1)&&counts[role][c]>=27){over=true;break;}
  if(over)continue;
  Bits bit=wtop[p]>=0?(Bits(1)<<(base+c)):0;if(used&bit)continue;
  v[p]=c;for(int role=0;role<4;role++)if(roles>>role&1)counts[role][c]++;
  visit(p+1,used|bit);
  for(int role=0;role<4;role++)if(roles>>role&1)counts[role][c]--;
  if(timedout)return;
 }
}
int main(int argc,char**argv){
 if(argc<5){cerr<<"Usage: search PREFIX_DIGITS ROWS SECONDS OUTPUT.jsonl\n";return 2;}
 fill(wtop,wtop+100,-1);
 for(int r=1;r<10;r++)for(int j=0;j<2*r-1;j++){
  int ps[]={(r-1)*(r-1)+j,r*r+j,r*r+j+1,r*r+j+2};
  wtop[ps[3]]=ps[0];for(int role=0;role<4;role++)roleMask[ps[role]]|=1<<role;
 }
 ifstream f("prefix_known.txt");string s;while(f>>s)known.insert(canonical(s));
 ifstream old("prefix_result.json");string line,b;while(getline(old,line))if(line.size()>2&&line[0]=='"'){auto end=line.find('"',1);b+=line.substr(1,end-1);}if(b.size()==100)known.insert(canonical(b));
 int rows=stoi(argv[2]),prefix_len=rows*rows;string pre=argv[1];Bits used=0;
 if(rows<0||pre.size()<static_cast<size_t>(prefix_len))return 2;
 for(int p=0;p<prefix_len;p++){
  v[p]=pre[p]-'0';if(v[p]<0||v[p]>2)return 2;
  for(int role=0;role<4;role++)if(roleMask[p]>>role&1)counts[role][v[p]]++;
  if(wtop[p]>=0){int code=27*v[wtop[p]]+9*v[p-2]+3*v[p-1]+v[p];Bits bit=Bits(1)<<code;if(used&bit){cerr<<"duplicate prefix"<<endl;return 2;}used|=bit;}
 }
 result.open(argv[4],ios::app);started=chrono::steady_clock::now();deadline=started+chrono::seconds(stoi(argv[3]));
 visit(prefix_len,used);
 cerr<<"FINAL rows="<<rows<<" nodes="<<nodes<<" solutions="<<sols<<" fresh_orbits="<<fresh<<" exhaustive="<<!timedout<<" elapsed="<<chrono::duration<double>(chrono::steady_clock::now()-started).count()<<endl;
 return timedout?1:0;
}

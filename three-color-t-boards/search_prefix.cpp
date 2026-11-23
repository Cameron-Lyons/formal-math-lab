// Independent depth-first certificate search; pattern order: top,left,middle,right.
#include <algorithm>
#include <array>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <unordered_set>
using namespace std;
int v[100], topc[3], wtop[100], rowpos[100], rstart[100];
unsigned long long nodes=0, sols=0;
int prefix_len=0;
chrono::steady_clock::time_point deadline;
unordered_set<string> known;
using Bits=unsigned __int128;
bool timedout=false;
bool visit(int p,Bits used){
 if((++nodes & 0xfffff)==0 && chrono::steady_clock::now()>deadline){timedout=true;return false;}
 if(p==100){
  ++sols; string s;for(int c:v)s.push_back('0'+c);
  if(known.count(s))return false;
  ofstream f("prefix_result.json");f<<"{\"rows\":[\n";
  for(int r=0;r<10;r++){if(r)f<<",\n";f<<'"'<<s.substr(r*r,2*r+1)<<'"';} f<<"\n],\"nodes\":"<<nodes<<",\"solutions_seen\":"<<sols<<"}\n";
  cout<<s<<endl;return true;
 }
 int base=wtop[p]>=0?27*v[wtop[p]]+9*v[p-2]+3*v[p-1]:0;
 for(int c=0;c<3;c++){
  if(p<81 && topc[c]>=27)continue;
  Bits bit=wtop[p]>=0?(Bits(1)<<(base+c)):0;
  if(used&bit)continue;
  v[p]=c;if(p<81)topc[c]++;
  bool found=visit(p+1,used|bit);
  if(p<81)topc[c]--;
  if(found)return true;
  if(timedout)return false;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc<4)return 2;
 fill(wtop,wtop+100,-1);
 for(int r=1;r<10;r++)for(int j=0;j<2*r-1;j++)wtop[r*r+j+2]=(r-1)*(r-1)+j;
 ifstream f("prefix_known.txt");string s;while(f>>s)known.insert(s);
 int rows=stoi(argv[2]);prefix_len=rows*rows;
 string pre=argv[1];
 Bits used=0;
 for(int p=0;p<prefix_len;p++){
  v[p]=pre[p]-'0';if(p<81)topc[v[p]]++;
  if(wtop[p]>=0){int code=27*v[wtop[p]]+9*v[p-2]+3*v[p-1]+v[p];Bits bit=Bits(1)<<code;if(used&bit){cerr<<"duplicate prefix"<<endl;return 2;}used|=bit;}
 }
 deadline=chrono::steady_clock::now()+chrono::seconds(stoi(argv[3]));
 bool ok=visit(prefix_len,used);
 cerr<<"rows="<<rows<<" nodes="<<nodes<<" known_solutions="<<sols<<" found="<<ok<<" timeout="<<timedout<<endl;
 return ok?0:1;
}

#include <bits/stdc++.h>
using namespace std;
vector<string> options[10];string current;set<string> published;
bool found=false;long long nodes=0;
void dfs(int r,__uint128_t used){
 ++nodes;if(found)return;
 if(r==10){if(!published.count(current)){ofstream o("search_local_result.txt");o<<current<<'\n';cerr<<"FOUND "<<nodes<<"\n";found=true;}return;}
 for(auto &s:options[r]){
  __uint128_t next=used;bool good=true;
  for(int j=0;j<2*r-1;j++){
   int code=(current[(r-1)*(r-1)+j]-'0')*27+(s[j]-'0')*9+(s[j+1]-'0')*3+s[j+2]-'0';
   __uint128_t bit=(__uint128_t)1<<code;
   if(next&bit){good=false;break;}next|=bit;
  }
  if(good){current+=s;dfs(r+1,next);current.resize(r*r);}
 }
}
int main(){
 ifstream f("search_local_seeds.txt");vector<string> seeds;string a;
 while(f>>a)seeds.push_back(a);
 for(auto a:seeds){array<int,3> p={0,1,2};do{for(int rev=0;rev<2;rev++){string s=a;for(int i=0;i<100;i++)s[i]='0'+p[a[i]-'0'];if(rev)for(int r=0;r<10;r++)reverse(s.begin()+r*r,s.begin()+(r+1)*(r+1));published.insert(s);}}while(next_permutation(p.begin(),p.end()));}
 for(auto seed:seeds){
  for(int r=0;r<10;r++){
   set<string> distinct;array<int,3> p={0,1,2};
   do{string row=seed.substr(r*r,2*r+1);for(char &c:row)c='0'+p[c-'0'];distinct.insert(row);reverse(row.begin(),row.end());distinct.insert(row);}while(next_permutation(p.begin(),p.end()));
   options[r]=vector<string>(distinct.begin(),distinct.end());
  }
  dfs(0,0);if(found)return 0;
 }
 cerr<<"no witness; nodes "<<nodes<<"\n";
}

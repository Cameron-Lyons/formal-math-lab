#include <bits/stdc++.h>
using namespace std;
mt19937 rng(20261122);
struct W {array<int,4> c;};
vector<W> windows;
vector<pair<int,int>> affect[100];
vector<string> seeds;
set<string> old;
int x[100], hist[81], codes[81];
int cost=0;
int change(int c,int nv,bool apply) {
 int delta=0;
 for(auto [w,p]:affect[c]) {int oc=codes[w];delta-=--hist[oc];}
 for(auto [w,p]:affect[c]) {int nc=codes[w]+p*(nv-x[c]);delta+=hist[nc]++;}
 if(apply) {for(auto [w,p]:affect[c])codes[w]+=p*(nv-x[c]);x[c]=nv;cost+=delta;}
 else {
  for(auto [w,p]:affect[c])hist[codes[w]+p*(nv-x[c])]--;
  for(auto [w,p]:affect[c])hist[codes[w]]++;
 }
 return delta;
}
void initialize(string s) {
 memset(hist,0,sizeof hist);cost=0;
 for(int i=0;i<100;i++)x[i]=s[i]-'0';
 for(int w=0;w<81;w++) {int v=0;for(int c:windows[w].c)v=3*v+x[c]; codes[w]=v; cost+=hist[v]++;}
}
int main(int argc,char**argv) {
 double seconds=argc>1?atof(argv[1]):120;
 for(int r=1;r<10;r++)for(int j=0;j<2*r-1;j++)windows.push_back({{(r-1)*(r-1)+j,r*r+j,r*r+j+1,r*r+j+2}});
 for(int w=0;w<81;w++){int p=27;for(int c:windows[w].c){affect[c].push_back({w,p});p/=3;}}
 ifstream f("search_local_seeds.txt");string s;
 while(f>>s)seeds.push_back(s);
 for(auto a:seeds){array<int,3> p={0,1,2};do{for(int rev=0;rev<2;rev++){s=a;for(int i=0;i<100;i++)s[i]='0'+p[a[i]-'0'];if(rev)for(int r=0;r<10;r++)reverse(s.begin()+r*r,s.begin()+(r+1)*(r+1));old.insert(s);}}while(next_permutation(p.begin(),p.end()));}
 auto start=chrono::steady_clock::now();long long moves=0;int runs=0,best=81;
 while(chrono::duration<double>(chrono::steady_clock::now()-start).count()<seconds){
  runs++;initialize(seeds[rng()%5]);
  // Retain early rows, but require one mutable cell to differ from this seed.
  int freeze=(runs%3==0?0:(runs%3==1?36:64));
  int anchor=freeze+rng()%(100-freeze),av=(x[anchor]+1+rng()%2)%3;
  change(anchor,av,true);
  for(int k=0;k<300000;k++){
   moves++;
   if(cost==0){s="";for(int i:x)s+=char('0'+i);if(!old.count(s)){ofstream o("search_local_result.txt");o<<s<<'\n';cerr<<"FOUND after "<<moves<<" moves\n";return 0;}break;}
   best=min(best,cost);
   if(moves%1000000==0 && chrono::duration<double>(chrono::steady_clock::now()-start).count()>=seconds)break;
   int w;do{w=rng()%81;}while(hist[codes[w]]<2);
   int c=windows[w].c[rng()%4];if(c<freeze||c==anchor)continue;
   int nv=(x[c]+1+rng()%2)%3;
   int d=change(c,nv,false);
   double t=0.12+0.65*(1.0-(k%30000)/30000.0);
   if(d<=0||generate_canonical<double,32>(rng)<exp(-d/t))change(c,nv,true);
  }
 }
 cerr<<"No witness; moves="<<moves<<" restarts="<<runs<<" best="<<best<<"\n";
}

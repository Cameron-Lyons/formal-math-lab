// Exact affine-CA subclass test for uniform 3-coordinate marginals.
// Every lower triple must occur n times. The nonzero affine coefficients then
// imply every 3-coordinate T marginal is uniform; T quadruples occur n or 0 times.
// Build: c++ -O3 -std=c++20 experiments/exact_structure_ca.cpp -o /tmp/exact_structure_ca
// Usage: exact_structure_ca N A B C D SECONDS ; N is 2 or 3.
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <cstdlib>
struct Search {
    int n,a,b,c,d,m,length;
    double seconds;
    std::array<std::array<int,19>,10> rows{};
    std::array<int,27> used{};
    std::array<std::uint64_t,20> levels{};
    std::uint64_t nodes=0, solutions=0;
    bool timeout=false;
    std::chrono::steady_clock::time_point started=std::chrono::steady_clock::now();
    Search(int N,int A,int B,int C,int D,double S):n(N),a(A),b(B),c(C),d(D),m(N*N),length(2*N*N+1),seconds(S){}
    void visit(int pos) {
        ++nodes; ++levels[pos];
        if ((nodes&262143u)==0 && seconds>0 &&
            std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()>=seconds) {
            timeout=true; return;
        }
        if (pos==length) {
            ++solutions;
            if (solutions==1) {
                std::cout<<"WITNESS\n";
                for(int r=0;r<=m;++r) {
                    for(int j=0;j<=2*r;++j) std::cout<<rows[r][j];
                    std::cout<<'\n';
                }
                std::cout.flush();
            }
            return;
        }
        for(int value=0;value<n && !timeout;++value) {
            rows[m][pos]=value;
            int j=pos, r=m, changed=0;
            std::array<int,9> undo{};
            bool okay=true;
            while(j>=2 && r>0) {
                int l=rows[r][j-2], mid=rows[r][j-1], right=rows[r][j];
                int code=n*n*l+n*mid+right;
                if(used[code]==n) {okay=false;break;}
                ++used[code]; undo[changed++]=code;
                rows[r-1][j-2]=(a*l+b*mid+c*right+d)%n;
                --r; j-=2;
            }
            if(okay) visit(pos+1);
            while(changed) --used[undo[--changed]];
        }
    }
};
int main(int argc,char **argv) {
    if(argc!=7) return 2;
    int n=std::atoi(argv[1]),a=std::atoi(argv[2]),b=std::atoi(argv[3]),c=std::atoi(argv[4]),d=std::atoi(argv[5]);
    if((n!=2&&n!=3)||a<=0||a>=n||b<=0||b>=n||c<=0||c>=n||d<0||d>=n) return 2;
    Search s(n,a,b,c,d,std::atof(argv[6])); s.visit(0);
    std::cout<<"colors="<<n<<" rule="<<a<<','<<b<<','<<c<<','<<d<<" status="<<(s.timeout?"INCOMPLETE":"COMPLETE")
             <<" solutions="<<s.solutions<<" nodes="<<s.nodes<<" seconds="
             <<std::chrono::duration<double>(std::chrono::steady_clock::now()-s.started).count()<<'\n';
    for(int i=0;i<=s.length;++i) std::cout<<"level "<<i<<' '<<s.levels[i]<<'\n';
}

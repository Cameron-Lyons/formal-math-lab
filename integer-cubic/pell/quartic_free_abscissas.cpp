#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_set>

using Vector = std::array<int,8>;

bool read(std::istream &in, Vector &v) {
    if (!(in >> v[0])) return false;
    for (int j=1; j<8; ++j) if (!(in >> v[j])) throw std::runtime_error("short residue vector");
    return true;
}

int key(const Vector &v,int p,int unit) {
    int r=0;
    for (int a:v) r=p*r+((a*unit)%p+p)%p;
    return r;
}

std::unordered_set<int> admissible(const std::string &path,int p) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("missing residue list");
    std::unordered_set<int> result;
    Vector v;
    while (read(in,v)) result.insert(key(v,p,1));
    return result;
}

int main(int argc,char **argv) {
    if (argc!=3) return 2;
    const int h=std::stoi(argv[1]);
    if (h<1 || h>171) return 2;
    const std::string dir=argv[2];
    const auto mod3=admissible(dir+"/r3",3), mod5=admissible(dir+"/r5",5);
    const std::array<int,5> inverse5={0,1,3,2,4};
    std::ifstream in(dir+"/r7"); std::ofstream out(dir+"/out");
    if (!in || !out) return 2;
    Vector r,a;
    std::uint64_t bounded=0,filtered=0,residues=0;
    while (read(in,r)) {
        ++residues;
        for (int d=1; d<=h; ++d) {
            if (d%7==0) continue;
            bool fits=true;
            for (int j=0; j<8; ++j) {
                int c=r[j]*d%343;
                a[j]=c>171 ? c-343 : c;
                if (a[j]>h || a[j]<-h) { fits=false; break; }
            }
            if (!fits) continue;
            int g=d;
            for (int c:a) g=std::gcd(g,c);
            if (g!=1) continue;
            ++bounded;
            if (d%5 && !mod5.count(key(a,5,inverse5[d%5]))) continue;
            if (d%3 && !mod3.count(key(a,3,d%3))) continue;
            ++filtered;
            out<<d; for (int c:a) out<<' '<<c; out<<'\n';
        }
    }
    std::cout<<"residues "<<residues<<", primitive bounded vectors "<<bounded
             <<", after mod 3 and 5 "<<filtered<<std::endl;
}

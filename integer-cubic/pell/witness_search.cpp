// g++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror witness_search.cpp -o /tmp/witness_search
// Arguments: max |z|, largest prime factor, quotient radius, min |z|, min |x|.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using Int = std::int64_t;
using Wide = __int128_t;

Int mod(Int x, Int n) {
    const Int r = x % n;
    return r < 0 ? r + n : r;
}

Int power(Int x, Int e, Int n) {
    Int r = 1;
    while (e > 0) {
        if (e % 2) r = r * x % n;
        x = x * x % n;
        e /= 2;
    }
    return r;
}

Int inverse(Int x, Int n) {
    Int u = 1, v = 0, y = n;
    while (y) {
        const Int q = x / y, remainder = x % y, next = u - q*v;
        x = y; y = remainder;
        u = v; v = next;
    }
    if (x != 1) throw std::logic_error("nonunit CRT argument");
    return mod(u,n);
}

std::vector<Int> primeRoots(Int p) {
    if (p == 2) return {0};
    if (p == 3) return {2};
    if (p % 3 == 2) return {power(2,(2*p-1)/3,p)};
    if (power(2,(p-1)/3,p) != 1) return {};
    // First take the inverse cube in the prime-to-three component.
    Int m = p-1;
    while (m % 3 == 0) m /= 3;
    const Int n = (p-1)/m;
    const Int e = (m % 3 == 1 ? 2*m+1 : m+1)/3;
    const Int y = power(2,e,p), h = 2*inverse(power(y,3,p),p)%p;
    // Correct in the cyclic 3-primary component.
    Int g = 1;
    for (Int j = 2; power(g,n/3,p) == 1; ++j) g = power(j,m,p);
    const Int step = power(g,3,p), unity = power(g,n/3,p);
    Int r = y;
    for (Int v = 1; v != h; v = v*step%p) r = r*g%p;
    return {r,r*unity%p,r*unity%p*unity%p};
}

struct PrimePower { Int modulus; std::vector<Int> roots; };

struct Search {
    Int maxZ, maxPrime, radius, minZ, minX;
    std::vector<std::vector<PrimePower>> factors{};
    std::array<bool,256> squares{};
    Int residues = 0, tested = 0;

    void initialize() {
        for (int i = 0; i < 256; ++i) squares[i*i%256] = true;
        std::vector<bool> sieve(maxPrime+1,true);
        for (Int p = 2; p <= maxPrime; ++p) {
            if (!sieve[p]) continue;
            for (Int j = p*p; j <= maxPrime; j += p) sieve[j] = false;
            auto roots = primeRoots(p);
            if (roots.empty()) continue;
            std::vector<PrimePower> powers;
            for (Int m = p; ; m *= p) {
                for (Int r : roots)
                    if ((Wide(r)*r*r-2)%m != 0) throw std::logic_error("cube root");
                powers.push_back({m, roots});
                if (p <= 3 || m > maxZ/p) break;
                for (Int &r : roots) {
                    const Int err = (Wide(r)*r*r-2)/m%p;
                    const Int derivative = 3*(r%p)*(r%p)%p;
                    r += m*mod(-err*inverse(derivative,p),p);
                }
            }
            factors.push_back(std::move(powers));
        }
    }

    void test(Int d, Int r) {
        if (d < minZ) return;
        ++residues;
        const Wide base = (Wide(r)*r*r-2)/d+d;
        const Wide rr = Wide(r)*r, rd = Wide(r)*d, dd = Wide(d)*d;
        for (Int q = -radius; q <= radius; ++q) {
            const Int x = r+q*d;
            if (std::abs(x) <= minX) continue;
            ++tested;
            const Wide s = base+q*(3*rr+q*(3*rd+q*dd));
            const Wide a = s < 0 ? -s : s;
            if (!squares[static_cast<unsigned>(a) & 255]) continue;
            Int y = static_cast<Int>(std::sqrt(static_cast<double>(a)));
            // Floating point supplies only an initial estimate.
            while (Wide(y)*y > a) --y;
            while (Wide(y+1)*(y+1) <= a) ++y;
            if (Wide(y)*y != a) continue;
            const Int z = s < 0 ? d : -d;
            std::cout << x << ' ' << y << ' ' << z << '\n' << std::flush;
            if (s == 0) std::cout << x << ' ' << y << ' ' << -z << '\n' << std::flush;
        }
    }

    void run(Int d, Int r, std::size_t start) {
        test(d,r);
        for (auto i = start; i < factors.size() && factors[i][0].modulus <= maxZ/d; ++i) {
            for (const auto &factor : factors[i]) {
                const Int m = factor.modulus;
                if (m > maxZ/d) break;
                const Int inv = d == 1 ? 1 : inverse(d%m,m);
                for (Int u : factor.roots) {
                    const Int digit = mod(mod(u-r,m)*inv,m);
                    run(d*m,r+digit*d,i+1);
                }
            }
        }
    }
};

int main(int argc, char **argv) {
    if (argc != 6) return 1;
    Search s{std::stoll(argv[1]),std::stoll(argv[2]),std::stoll(argv[3]),
             std::stoll(argv[4]),std::stoll(argv[5])};
    // These ranges keep the CRT products in Int and polynomial values in Wide.
    if (s.maxZ < 1 || s.maxZ > 2000000000 || s.maxPrime < 2 ||
        s.maxPrime > std::min<Int>(s.maxZ,10000000) || s.radius < 0 ||
        s.radius > 10000 || s.minZ < 1 || s.minZ > s.maxZ || s.minX < 0) return 1;
    s.initialize();
    s.run(1,0,0);
    std::cerr << s.residues << " root classes, " << s.tested << " square tests\n";
}

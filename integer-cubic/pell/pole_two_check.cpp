// c++ -O3 -std=c++17 pole_two_check.cpp -o /tmp/pole_two_check && /tmp/pole_two_check
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

namespace {
constexpr int p = 13;
using Poly = std::array<int, 13>; // coefficients of T^0 through T^12
using Matrix = std::array<Poly, 13>;

void require(bool condition, const char* message) {
    if (!condition) throw std::runtime_error(message);
}

// In the quadratic field, a + b*sqrt(2) is stored as a + 13*b.
struct Field {
    int size;
    std::uint8_t sum[169][169]{}, product[169][169]{};
    std::array<int, 169> negative{}, root{}, inverse{}, conjugate{}, norm{};

    explicit Field(int q) : size(q) {
        root.fill(-1);
        for (int a = 0; a < q; ++a) {
            for (int b = 0; b < q; ++b) {
                int x = a % p, y = a / p, z = b % p, w = b / p;
                sum[a][b] = (x+z)%p + p*((y+w)%p);
                product[a][b] = (x*z+2*y*w)%p + p*((x*w+y*z)%p);
            }
        }
        for (int a = 0; a < q; ++a) {
            negative[a] = product[12][a];
            root[product[a][a]] = a;
            inverse[a] = power(a, q-2);
            conjugate[a] = a%p + p*((p-a/p)%p);
            norm[a] = product[a][conjugate[a]];
            if (a) require(product[a][inverse[a]] == 1, "invalid field inverse");
        }
    }
    int sub(int a, int b) const { return sum[a][negative[b]]; }
    int power(int base, int n) const {
        int r = 1;
        while (n) {
            if (n%2) r = product[r][base];
            base = product[base][base];
            n /= 2;
        }
        return r;
    }
    int eval(const Poly& f, int t, int degree = 12) const {
        int r = 0;
        for (int i = degree; i >= 0; --i) r = sum[product[r][t]][f[i]];
        return r;
    }
    Poly mul(const Poly& f, const Poly& g, int m, int n) const {
        Poly h{};
        for (int i = 0; i <= m; ++i)
            for (int j = 0; j <= n; ++j)
                h[i+j] = sum[h[i+j]][product[f[i]][g[j]]];
        return h;
    }
    // Recover a putative root from its leading coefficient, then multiply it out.
    bool squareRoot(const Poly& f, Poly& w) const {
        int top = 12;
        while (top >= 0 && f[top] == 0) --top;
        w = {};
        if (top < 0) return true;
        if (top%2 || root[f[top]] < 0) return false;
        int d = top/2;
        w[d] = root[f[top]];
        int scale = inverse[product[2][w[d]]];
        for (int k = d-1; k >= 0; --k) {
            int value = f[d+k];
            for (int j = k+1; j < d; ++j)
                value = sub(value,product[w[j]][w[d+k-j]]);
            w[k] = product[scale][value];
        }
        return mul(w,w,d,d) == f;
    }
    bool invertible(Matrix m) const {
        for (int j = 0; j < 13; ++j) {
            int i = j;
            while (i < 13 && m[i][j] == 0) ++i;
            if (i == 13) return false;
            std::swap(m[i], m[j]);
            for (i = j+1; i < 13; ++i) {
                int factor = product[m[i][j]][inverse[m[j][j]]];
                for (int k = j; k < 13; ++k)
                    m[i][k] = sub(m[i][k],product[factor][m[j][k]]);
            }
        }
        return true;
    }
};

// X=T²x, Y=T y, W=T³w for Laurent functions. Setting shift=0 instead
// tests w²=y⁴+8−4x³ for ordinary polynomials.
Poly discriminant(const Field& k, const Poly& x, const Poly& y, int shift) {
    auto cube = k.mul(k.mul(x,x,4,4),x,8,4);
    auto ys = k.mul(y,y,2,2);
    auto fourth = k.mul(ys,ys,4,4);
    Poly f{};
    for (int i = 0; i <= 12; ++i) f[i] = k.product[9][cube[i]]; // −4
    for (int i = 0; i <= 8; ++i) f[i+shift] = k.sum[f[i+shift]][fourth[i]];
    f[3*shift] = k.sum[f[3*shift]][8];
    return f;
}

// Assert that both involutions fix the point, and that fixing c leaves
// an invertible Jacobian of the thirteen coefficient equations.
void certifyLaurentRoot(const Field& k, const Poly& x, const Poly& y, const Poly& w) {
    int c = y[0];
    require(c && y[1] == 0 && x[1] == 0 && x[3] == 0, "unexpected odd term or pole");
    require(k.product[k.power(c,2)][x[4]] == x[0], "x is not invariant under T -> c/T");
    for (int j = 0; j < 3; ++j) {
        require(w[2*j+1] == 0, "W has wrong parity");
        int l = 3-j;
        require(w[j] == k.negative[k.product[k.power(c,l)][w[6-j]]],
                "w is not anti-invariant under T -> c/T");
    }
    auto ys = k.mul(k.mul(y,y,2,2),y,4,2);
    auto xs = k.mul(x,x,4,4);
    Matrix jac{};
    for (int j = 0; j <= 6; ++j) jac[j+3][0] = k.product[9][ys[j]];
    for (int i = 0; i <= 4; ++i)
        for (int j = 0; j <= 8; ++j) jac[i+j][1+i] = k.product[12][xs[j]];
    for (int i = 0; i <= 6; ++i)
        for (int j = 0; j <= 6; ++j) jac[i+j][6+i] = k.product[2][w[j]];
    require(k.invertible(jac), "singular Laurent point");
}

// Evaluation at field points is only an early rejection. Every surviving
// candidate is tested by multiplying polynomials coefficient by coefficient.
void ordinary(const Field& k) {
    int degree = k.size == p ? 4 : 2;
    std::vector<Poly> ys{{0,1}};
    if (k.size == p) {
        for (int a : {1,2})
            for (int b = 0; b < p; ++b) ys.push_back({b,0,a});
    }
    std::vector<Poly> values;
    for (const auto& y : ys) {
        Poly v{};
        for (int t = 0; t < p; ++t) v[t] = k.sum[k.power(k.eval(y,t,2),4)][8];
        values.push_back(v);
    }
    int n = 1;
    for (int i = 0; i <= degree; ++i) n *= k.size;
    std::int64_t tested = 0;
    for (int code = 0; code < n; ++code) {
        int rest = code;
        Poly x{}, cube{};
        for (int j = 0; j <= degree; ++j) { x[j] = rest%k.size; rest /= k.size; }
        for (int t = 0; t < p; ++t) cube[t] = k.product[9][k.power(k.eval(x,t,degree),3)];
        for (std::size_t i = 0; i < ys.size(); ++i) {
            ++tested;
            int t = 0;
            while (t < p && k.root[k.sum[values[i][t]][cube[t]]] >= 0) ++t;
            if (t < p) continue;
            Poly w{};
            require(!k.squareRoot(discriminant(k,x,ys[i],0),w), "ordinary polynomial solution");
        }
    }
    for (int y = 0; y < k.size; ++y)
        require(k.sum[k.power(y,4)][8] != 0, "singular constant-y fiber");
    std::cout << "F" << k.size << " ordinary: " << tested << " pairs, zero squares\n";
}

void laurent(const Field& k) {
    bool split = k.size == p;
    std::int64_t tested = 0, hits = 0;
    for (int c = split ? 0 : 1; c < p; ++c) {
        std::vector<int> ts;
        for (int t = 1; t < k.size; ++t)
            if (split || k.norm[t] == c) ts.push_back(t);
        std::array<std::vector<int>,p> yvalues;
        for (int b = 0; b < p; ++b)
            for (int t : ts) {
                int y = k.sum[k.sum[t][b]][k.product[c][k.inverse[t]]];
                yvalues[b].push_back(k.sum[k.power(y,4)][8]);
            }
        auto visit = [&](const Poly& x) {
            // At nonzero rational torus points the discriminant must be
            // a square in the prime field, also in the inert case.
            std::array<int,14> cube{};
            for (std::size_t j = 0; j < ts.size(); ++j) {
                int t = ts[j];
                int xv = k.product[k.eval(x,t,4)][k.power(k.inverse[t],2)];
                require(xv < p, "x does not descend");
                cube[j] = k.product[9][k.power(xv,3)];
            }
            for (int b = 0; b < p; ++b) {
                ++tested;
                std::size_t j = 0;
                for (; j < ts.size(); ++j) {
                    int d = k.sum[yvalues[b][j]][cube[j]];
                    if (d && k.power(d,6) != 1) break;
                }
                if (j != ts.size()) continue;
                Poly y{c,b,1}, w{};
                if (!k.squareRoot(discriminant(k,x,y,2),w)) continue;
                certifyLaurentRoot(k,x,y,w);
                ++hits;
            }
        };
        if (split) {
            // y has a pole at infinity. At any surviving pole of y, x has
            // order two by its two leading coefficient equations.
            for (int x4 = 1; x4 < p; ++x4) {
                if (k.root[x4] < 0) continue;
                for (int x0 = c ? 1 : 0; x0 < p; ++x0) {
                    if (k.root[x0] < 0) continue;
                    for (int x1 = 0; x1 < p; ++x1)
                        for (int x2 = 0; x2 < p; ++x2)
                            for (int x3 = 0; x3 < p; ++x3) visit({x0,x1,x2,x3,x4});
                }
            }
        } else {
            for (int a = 1; a < k.size; ++a) {
                if (k.root[a] < 0) continue;
                for (int d = 0; d < k.size; ++d)
                    for (int b = 0; b < p; ++b)
                        visit({k.product[c*c%p][k.conjugate[a]],k.product[c][k.conjugate[d]],b,d,a});
            }
        }
    }
    require(hits == (split ? 6 : 12), "unexpected Laurent count");
    std::cout << "F" << k.size << " Laurent: " << tested << " pairs, " << hits
              << " square discriminants with certified symmetries and Jacobians\n";
}
} // namespace

int main() {
    Field prime(13), quadratic(169);
    ordinary(prime);
    ordinary(quadratic);
    laurent(prime);
    laurent(quadratic);
}

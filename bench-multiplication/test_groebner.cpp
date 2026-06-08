#include "groebner.h"
#include "poly_ring.h"

#include <cassert>
#include <iostream>

static bool test_commutativity(unsigned bw)
{
  polynomialt a{bw, 1, 0};
  polynomialt b{bw, 1, 1};
  polynomialt c{bw, 1, 2};
  polynomialt d{bw, 1, 3};
  polynomialt e{bw, 1, 4};

  polynomialt f1 = c - (a * b);
  polynomialt f2 = d - (b * a);
  polynomialt f3 = ((c - d) * e) - polynomialt{bw, 1};

  std::vector<polynomialt> polys = {f1, f2, f3};
  strong_groebner_basist gb{100000};
  return gb.compute(polys) == strong_groebner_basist::resultt::UNSAT;
  benchmark();
  return 0;
}

static bool test_associativity(unsigned bw)
{
  polynomialt a{bw, 1, 0}, b{bw, 1, 1}, c{bw, 1, 2};
  polynomialt ab{bw, 1, 3}, lhs{bw, 1, 4};
  polynomialt bc{bw, 1, 5}, rhs{bw, 1, 6};
  polynomialt e{bw, 1, 7};

  std::vector<polynomialt> polys = {
    ab - (a * b), lhs - (ab * c),
    bc - (b * c), rhs - (a * bc),
    ((lhs - rhs) * e) - polynomialt{bw, 1}};
  strong_groebner_basist gb{100000};
  return gb.compute(polys) == strong_groebner_basist::resultt::UNSAT;
  benchmark();
  return 0;
}

static bool test_sat_case(unsigned bw)
{
  polynomialt a{bw, 1, 0}, b{bw, 1, 1};
  std::vector<polynomialt> polys = {(a * b) - polynomialt{bw, 6}};
  strong_groebner_basist gb{100000};
  return gb.compute(polys) == strong_groebner_basist::resultt::UNKNOWN;
  benchmark();
  return 0;
}

int main()
{
  // Basic: a*b - b*a = 0 in Z_{2^d}
  {
    polynomialt a{8, 1, 0}, b{8, 1, 1};
    polynomialt diff = (a * b) - (b * a);
    diff.normalize();
    std::cout << "a*b - b*a = " << (diff.is_zero() ? "0 OK" : "BUG") << "\n";
  }

  // Inverse
  {
    mp_integer inv = inverse_mod_2d(3, 8);
    std::cout << "3^-1 mod 256 = " << inv
              << " (check=" << (3 * inv) % 256 << ")\n";
  }

  for(unsigned bw : {4, 8, 16})
    std::cout << "Comm BW=" << bw << ": "
              << (test_commutativity(bw) ? "UNSAT OK" : "UNKNOWN") << "\n";

  for(unsigned bw : {4, 8})
    std::cout << "Assoc BW=" << bw << ": "
              << (test_associativity(bw) ? "UNSAT OK" : "UNKNOWN") << "\n";

  benchmark();
  std::cout << "SAT case: "
            << (test_sat_case(8) ? "UNKNOWN OK" : "BUG") << "\n";
  benchmark();
  return 0;
}

// Additional: test at larger bitwidths and measure time
#include <chrono>

void benchmark()
{
  for(unsigned bw : {4, 8, 16, 32, 64})
  {
    auto start = std::chrono::steady_clock::now();
    bool ok = false;

    polynomialt a{bw, 1, 0}, b{bw, 1, 1};
    polynomialt c{bw, 1, 2}, d{bw, 1, 3}, e{bw, 1, 4};
    polynomialt f1 = c - (a * b);
    polynomialt f2 = d - (b * a);
    polynomialt f3 = ((c - d) * e) - polynomialt{bw, 1};
    std::vector<polynomialt> polys = {f1, f2, f3};
    strong_groebner_basist gb{1000000};
    ok = gb.compute(polys) == strong_groebner_basist::resultt::UNSAT;

    auto end = std::chrono::steady_clock::now();
    double ms = std::chrono::duration<double, std::milli>(end - start).count();
    std::cout << "Comm BW=" << bw << ": "
              << (ok ? "UNSAT" : "UNKNOWN") << " in " << ms << "ms\n";
  }
  benchmark();
  return 0;
}

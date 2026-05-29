/// \file
/// Synthetic benchmark for polynomial Karatsuba.
/// Compares schoolbook_multiply vs operator* (which dispatches to
/// Karatsuba above threshold) on dense univariate polynomials.

#include <solvers/algebraic/poly_ring.h>

#include <chrono>
#include <iostream>

using sclock = std::chrono::steady_clock;

static polynomialt
random_dense(unsigned bw, std::size_t var, std::size_t degree)
{
  polynomialt p{bw};
  for(std::size_t i = 0; i <= degree; ++i)
  {
    monomialt mon;
    if(i > 0)
      mon.vars.emplace_back(var, static_cast<unsigned>(i));
    // Pseudorandom-ish nonzero coefficient
    mp_integer c{(std::int64_t)(1 + (i * 37 + 13) % 251)};
    p.terms.emplace_back(c, mon);
  }
  // p is already in grevlex order by construction (degree
  // descending: highest first since smaller degree => "smaller"
  // monomial in grevlex). Actually grevlex: higher TOTAL degree
  // is "larger" (comes first). So p.terms.front() should be
  // x^degree. Reverse.
  std::reverse(p.terms.begin(), p.terms.end());
  return p;
}

int main()
{
  const unsigned bw = 32;
  for(std::size_t deg : {32, 64, 128, 256, 512, 1024})
  {
    polynomialt f = random_dense(bw, 0, deg);
    polynomialt g = random_dense(bw, 0, deg);

    auto t0 = sclock::now();
    polynomialt h_kara = f * g; // dispatches to Karatsuba above threshold
    auto t1 = sclock::now();

    auto t2 = sclock::now();
    polynomialt h_school = f.schoolbook_multiply(g);
    auto t3 = sclock::now();

    auto kara_ms = std::chrono::duration_cast<std::chrono::microseconds>(
                     t1 - t0)
                     .count();
    auto school_ms = std::chrono::duration_cast<std::chrono::microseconds>(
                       t3 - t2)
                       .count();

    bool agree = (h_kara.terms.size() == h_school.terms.size());
    if(agree)
    {
      for(std::size_t i = 0; i < h_kara.terms.size(); ++i)
      {
        if(h_kara.terms[i].first != h_school.terms[i].first ||
           !(h_kara.terms[i].second == h_school.terms[i].second))
        {
          agree = false;
          break;
        }
      }
    }

    std::cout << "deg=" << deg
              << "  kara=" << kara_ms << "us  school=" << school_ms << "us"
              << "  speedup=" << (school_ms / std::max<std::int64_t>(1, kara_ms))
              << "x  agree=" << (agree ? "yes" : "NO") << "\n";
  }
  return 0;
}

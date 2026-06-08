// Distributivity through opaque store (defeats the simplifier's
// expression-level rewrite). Tests bv_refinementt::detect_algebraic_pairs'
// distributivity branch.
#include <stdint.h>

uint64_t store(uint64_t x)
{
  return x;
}

int main(void)
{
  uint16_t a, b, c;
  // Inner sum visible; outer mult result laundered.
  uint64_t lhs = store((uint64_t)a * ((uint64_t)b + (uint64_t)c));
  uint64_t rhs = store((uint64_t)a * (uint64_t)b)
              + store((uint64_t)a * (uint64_t)c);
  __CPROVER_assert(lhs == rhs, "distributivity");
  return 0;
}

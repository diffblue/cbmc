// Verify --refine-arithmetic detects commutativity and
// associativity through opaque stored intermediates.
//
// Without bv_refinementt::detect_algebraic_pairs, all three
// assertions time out at uint16 because the SAT solver must
// independently verify two bit-blasted multipliers. With pair
// detection, each pair's results are asserted equal up front
// and the solver dispatches each assertion in a single iteration.

#include <stdint.h>

uint64_t store(uint64_t x)
{
  return x;
}

void test_stored_commutativity(void)
{
  uint16_t a, b;
  uint64_t p = store((uint64_t)a * (uint64_t)b);
  uint64_t q = store((uint64_t)b * (uint64_t)a);
  __CPROVER_assert(p == q, "stored commutativity");
}

void test_subtractive_commutativity(void)
{
  uint16_t a, b;
  uint16_t diff = (uint16_t)(a * b) - (uint16_t)(b * a);
  __CPROVER_assert(diff == 0, "subtractive commutativity");
}

void test_stored_associativity(void)
{
  uint16_t a, b, c;
  uint64_t ab = store((uint64_t)a * (uint64_t)b);
  uint64_t left = store(ab * (uint64_t)c);
  uint64_t bc = store((uint64_t)b * (uint64_t)c);
  uint64_t right = store((uint64_t)a * bc);
  __CPROVER_assert(left == right, "stored associativity");
}

int main(void)
{
  test_stored_commutativity();
  test_subtractive_commutativity();
  test_stored_associativity();
  return 0;
}

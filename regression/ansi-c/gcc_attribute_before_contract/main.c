// Test for issue #8685: GCC attributes before contract clauses
// This test verifies that GCC __attribute__ syntax can appear before
// __CPROVER_* contract clauses, just like C23 [[...]] attributes.

#include <limits.h>

// Test 1: GCC attribute before __CPROVER_requires (declaration)
int test_decl1(int a) __attribute__((const)) __CPROVER_requires(a != 0);

// Test 2: GCC attribute before __CPROVER_ensures (declaration)
int test_decl2(int a) __attribute__((pure))
__CPROVER_ensures(__CPROVER_return_value > 0);

// Test 3: Multiple GCC attributes before __CPROVER_requires
int test_decl3(int a) __attribute__((const)) __attribute__((nonnull))
__CPROVER_requires(a != 0);

// Test 4: GCC attribute before multiple contract clauses
int test_decl4(int a) __attribute__((const)) __CPROVER_requires(a > 0)
  __CPROVER_ensures(__CPROVER_return_value == a + 1);

// Test 5: Function with no parameters, GCC attribute before contract
int test_decl5(void) __attribute__((const))
__CPROVER_ensures(__CPROVER_return_value == 42);

// Test 6: C23 attribute style (should still work as before)
int test_decl6(int a) [[gnu::const]] __CPROVER_requires(a != 0);

// Test 7: Function definition with GCC attribute and contract
int test_def1(int a) __attribute__((const)) __CPROVER_requires(a < INT_MAX)
{
  return a + 1;
}

// Test 8: No attribute (baseline - should still work)
int test_decl7(int a) __CPROVER_requires(a != 0);

// Test 9: Attribute without contract (should still work)
int test_decl8(int a) __attribute__((const));

int main(void)
{
  int x = 5;
  int result = test_def1(x);
  __CPROVER_assert(result == 6, "test_def1 should return 6");
  return 0;
}

unsigned long long nondet_ulonglong(void);

int main()
{
  unsigned long long x = nondet_ulonglong(), y = nondet_ulonglong();
  __CPROVER_assume(x > 1 && y > 1 && x < 0xFFFFFFFFull && y < 0xFFFFFFFFull);
  // 2654435761 * 2246822519, the product of two primes: factoring it takes
  // the solvers far longer than the time limit.
  __CPROVER_assert(x * y != 5964046043053701959ull, "not factored");
  return 0;
}

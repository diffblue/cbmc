int main()
{
  _Atomic(int) a;
  __c11_atomic_store(&a, 5, 5);
  __CPROVER_assert(__c11_atomic_load(&a, 5) == 5, "store then load");
  __CPROVER_assert(
    __c11_atomic_fetch_add(&a, 3, 5) == 5 && __c11_atomic_load(&a, 5) == 8,
    "fetch_add");
  __CPROVER_assert(__c11_atomic_load(&a, 5) == 9, "WRONG (must FAIL)");
  return 0;
}

// GCC's __atomic_* and __sync_* builtins (GCC reference, "Built-in Functions
// for Memory Model Aware Atomic Operations") are polymorphic; the front end
// materializes one implementation per instantiated type (c_typecheck_gcc_
// polymorphic_builtins.cpp).  In C++ every one of them failed: the synthesized
// body names CPROVER primitives (`__CPROVER_atomic_begin') and other builtins
// (`__atomic_load') by TYPELESS symbol expressions the C type checker resolves
// on the fly, and the C++ type checker left them as they were ("function call
// expects function or function pointer as argument"; "address_of error:
// 'result' not an lvalue").  libstdc++ uses them in __gnu_cxx::__atomic_add
// (shared_ptr, locale facets) -- every such program was a CONVERSION ERROR.
extern "C" void __CPROVER_assert(bool, const char *);
int counter = 5;
long big = 100;
int main()
{
  int old = __atomic_fetch_add(&counter, 3, __ATOMIC_ACQ_REL);
  __CPROVER_assert(old == 5 && counter == 8, "fetch_add");
  int now = __atomic_add_fetch(&counter, 2, __ATOMIC_SEQ_CST);
  __CPROVER_assert(now == 10, "add_fetch");
  __CPROVER_assert(__atomic_load_n(&counter, __ATOMIC_ACQUIRE) == 10, "load_n");
  __atomic_store_n(&counter, 1, __ATOMIC_RELEASE);
  __CPROVER_assert(counter == 1, "store_n");
  long oldbig = __atomic_fetch_sub(&big, 1, __ATOMIC_RELAXED);
  __CPROVER_assert(oldbig == 100 && big == 99, "fetch_sub on long");
  int expected = 1;
  bool ok = __atomic_compare_exchange_n(
    &counter, &expected, 7, false, __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
  __CPROVER_assert(ok && counter == 7, "compare_exchange_n");
  __CPROVER_assert(
    __sync_fetch_and_add(&counter, 1) == 7 && counter == 8,
    "__sync_fetch_and_add");
  __CPROVER_assert(counter == 9, "WRONG (must FAIL)");
}

typedef long long __gcc_v2di __attribute__((__vector_size__(16)));
typedef unsigned long long __gcc_v2di_u __attribute__((__vector_size__(16)));
__gcc_v2di __builtin_ia32_psubq128(__gcc_v2di, __gcc_v2di);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native -) for all inputs.
  __gcc_v2di a, b;
  __gcc_v2di r = __builtin_ia32_psubq128(a, b);
  __gcc_v2di_u ref = (__gcc_v2di_u)a - (__gcc_v2di_u)b;
  __CPROVER_assert(
    r[0] == (long long)ref[0] && r[1] == (long long)ref[1],
    "__builtin_ia32_psubq128 == native -");
  return 0;
}

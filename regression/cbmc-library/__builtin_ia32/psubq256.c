typedef long long __gcc_v4di __attribute__((__vector_size__(32)));
typedef unsigned long long __gcc_v4di_u __attribute__((__vector_size__(32)));
__gcc_v4di __builtin_ia32_psubq256(__gcc_v4di, __gcc_v4di);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native -) for all inputs.
  __gcc_v4di a, b;
  __gcc_v4di r = __builtin_ia32_psubq256(a, b);
  __gcc_v4di_u ref = (__gcc_v4di_u)a - (__gcc_v4di_u)b;
  __CPROVER_assert(
    r[0] == (long long)ref[0] && r[1] == (long long)ref[1] &&
      r[2] == (long long)ref[2] && r[3] == (long long)ref[3],
    "__builtin_ia32_psubq256 == native -");
  return 0;
}

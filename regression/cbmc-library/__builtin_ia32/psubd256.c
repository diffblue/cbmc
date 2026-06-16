typedef int __gcc_v8si __attribute__((__vector_size__(32)));
typedef unsigned int __gcc_v8si_u __attribute__((__vector_size__(32)));
__gcc_v8si __builtin_ia32_psubd256(__gcc_v8si, __gcc_v8si);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native -) for all inputs.
  __gcc_v8si a, b;
  __gcc_v8si r = __builtin_ia32_psubd256(a, b);
  __gcc_v8si_u ref = (__gcc_v8si_u)a - (__gcc_v8si_u)b;
  __CPROVER_assert(
    r[0] == (int)ref[0] && r[1] == (int)ref[1] && r[2] == (int)ref[2] &&
      r[3] == (int)ref[3] && r[4] == (int)ref[4] && r[5] == (int)ref[5] &&
      r[6] == (int)ref[6] && r[7] == (int)ref[7],
    "__builtin_ia32_psubd256 == native -");
  return 0;
}

typedef short __gcc_v16hi __attribute__((__vector_size__(32)));
typedef unsigned short __gcc_v16hi_u __attribute__((__vector_size__(32)));
__gcc_v16hi __builtin_ia32_paddw256(__gcc_v16hi, __gcc_v16hi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native +) for all inputs.
  __gcc_v16hi a, b;
  __gcc_v16hi r = __builtin_ia32_paddw256(a, b);
  __gcc_v16hi_u ref = (__gcc_v16hi_u)a + (__gcc_v16hi_u)b;
  __CPROVER_assert(
    r[0] == (short)ref[0] && r[1] == (short)ref[1] && r[2] == (short)ref[2] &&
      r[3] == (short)ref[3] && r[4] == (short)ref[4] && r[5] == (short)ref[5] &&
      r[6] == (short)ref[6] && r[7] == (short)ref[7] && r[8] == (short)ref[8] &&
      r[9] == (short)ref[9] && r[10] == (short)ref[10] &&
      r[11] == (short)ref[11] && r[12] == (short)ref[12] &&
      r[13] == (short)ref[13] && r[14] == (short)ref[14] &&
      r[15] == (short)ref[15],
    "__builtin_ia32_paddw256 == native +");
  return 0;
}

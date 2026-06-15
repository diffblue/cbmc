typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
typedef unsigned short __gcc_v8hi_u __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_paddw128(__gcc_v8hi, __gcc_v8hi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native +) for all inputs.
  __gcc_v8hi a, b;
  __gcc_v8hi r = __builtin_ia32_paddw128(a, b);
  __gcc_v8hi_u ref = (__gcc_v8hi_u)a + (__gcc_v8hi_u)b;
  __CPROVER_assert(
    r[0] == (short)ref[0] && r[1] == (short)ref[1] && r[2] == (short)ref[2] &&
      r[3] == (short)ref[3] && r[4] == (short)ref[4] && r[5] == (short)ref[5] &&
      r[6] == (short)ref[6] && r[7] == (short)ref[7],
    "__builtin_ia32_paddw128 == native +");
  return 0;
}

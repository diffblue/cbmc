typedef short __gcc_v4hi __attribute__((__vector_size__(8)));
typedef unsigned short __gcc_v4hi_u __attribute__((__vector_size__(8)));
__gcc_v4hi __builtin_ia32_paddw(__gcc_v4hi, __gcc_v4hi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native +) for all inputs.
  __gcc_v4hi a, b;
  __gcc_v4hi r = __builtin_ia32_paddw(a, b);
  __gcc_v4hi_u ref = (__gcc_v4hi_u)a + (__gcc_v4hi_u)b;
  __CPROVER_assert(
    r[0] == (short)ref[0] && r[1] == (short)ref[1] && r[2] == (short)ref[2] &&
      r[3] == (short)ref[3],
    "__builtin_ia32_paddw == native +");
  return 0;
}

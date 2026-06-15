typedef char __gcc_v8qi __attribute__((__vector_size__(8)));
typedef unsigned char __gcc_v8qi_u __attribute__((__vector_size__(8)));
__gcc_v8qi __builtin_ia32_psubb(__gcc_v8qi, __gcc_v8qi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native -) for all inputs.
  __gcc_v8qi a, b;
  __gcc_v8qi r = __builtin_ia32_psubb(a, b);
  __gcc_v8qi_u ref = (__gcc_v8qi_u)a - (__gcc_v8qi_u)b;
  __CPROVER_assert(
    r[0] == (char)ref[0] && r[1] == (char)ref[1] && r[2] == (char)ref[2] &&
      r[3] == (char)ref[3] && r[4] == (char)ref[4] && r[5] == (char)ref[5] &&
      r[6] == (char)ref[6] && r[7] == (char)ref[7],
    "__builtin_ia32_psubb == native -");
  return 0;
}

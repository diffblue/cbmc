typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
typedef unsigned char __gcc_v16qi_u __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_psubb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native -) for all inputs.
  __gcc_v16qi a, b;
  __gcc_v16qi r = __builtin_ia32_psubb128(a, b);
  __gcc_v16qi_u ref = (__gcc_v16qi_u)a - (__gcc_v16qi_u)b;
  __CPROVER_assert(
    r[0] == (char)ref[0] && r[1] == (char)ref[1] && r[2] == (char)ref[2] &&
      r[3] == (char)ref[3] && r[4] == (char)ref[4] && r[5] == (char)ref[5] &&
      r[6] == (char)ref[6] && r[7] == (char)ref[7] && r[8] == (char)ref[8] &&
      r[9] == (char)ref[9] && r[10] == (char)ref[10] &&
      r[11] == (char)ref[11] && r[12] == (char)ref[12] &&
      r[13] == (char)ref[13] && r[14] == (char)ref[14] &&
      r[15] == (char)ref[15],
    "__builtin_ia32_psubb128 == native -");
  return 0;
}

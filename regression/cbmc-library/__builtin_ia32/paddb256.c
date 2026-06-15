typedef char __gcc_v32qi __attribute__((__vector_size__(32)));
typedef unsigned char __gcc_v32qi_u __attribute__((__vector_size__(32)));
__gcc_v32qi __builtin_ia32_paddb256(__gcc_v32qi, __gcc_v32qi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native +) for all inputs.
  __gcc_v32qi a, b;
  __gcc_v32qi r = __builtin_ia32_paddb256(a, b);
  __gcc_v32qi_u ref = (__gcc_v32qi_u)a + (__gcc_v32qi_u)b;
  __CPROVER_assert(
    r[0] == (char)ref[0] && r[1] == (char)ref[1] && r[2] == (char)ref[2] &&
      r[3] == (char)ref[3] && r[4] == (char)ref[4] && r[5] == (char)ref[5] &&
      r[6] == (char)ref[6] && r[7] == (char)ref[7] && r[8] == (char)ref[8] &&
      r[9] == (char)ref[9] && r[10] == (char)ref[10] &&
      r[11] == (char)ref[11] && r[12] == (char)ref[12] &&
      r[13] == (char)ref[13] && r[14] == (char)ref[14] &&
      r[15] == (char)ref[15] && r[16] == (char)ref[16] &&
      r[17] == (char)ref[17] && r[18] == (char)ref[18] &&
      r[19] == (char)ref[19] && r[20] == (char)ref[20] &&
      r[21] == (char)ref[21] && r[22] == (char)ref[22] &&
      r[23] == (char)ref[23] && r[24] == (char)ref[24] &&
      r[25] == (char)ref[25] && r[26] == (char)ref[26] &&
      r[27] == (char)ref[27] && r[28] == (char)ref[28] &&
      r[29] == (char)ref[29] && r[30] == (char)ref[30] &&
      r[31] == (char)ref[31],
    "__builtin_ia32_paddb256 == native +");
  return 0;
}

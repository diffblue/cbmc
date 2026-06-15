typedef char __gcc_v32qi __attribute__((__vector_size__(32)));
__gcc_v32qi __builtin_ia32_pcmpgtb256(__gcc_v32qi, __gcc_v32qi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native >) for all inputs.
  __gcc_v32qi a, b;
  __gcc_v32qi r = __builtin_ia32_pcmpgtb256(a, b);
  __gcc_v32qi ref = a > b;
  __CPROVER_assert(
    r[0] == ref[0] && r[1] == ref[1] && r[2] == ref[2] && r[3] == ref[3] &&
      r[4] == ref[4] && r[5] == ref[5] && r[6] == ref[6] && r[7] == ref[7] &&
      r[8] == ref[8] && r[9] == ref[9] && r[10] == ref[10] &&
      r[11] == ref[11] && r[12] == ref[12] && r[13] == ref[13] &&
      r[14] == ref[14] && r[15] == ref[15] && r[16] == ref[16] &&
      r[17] == ref[17] && r[18] == ref[18] && r[19] == ref[19] &&
      r[20] == ref[20] && r[21] == ref[21] && r[22] == ref[22] &&
      r[23] == ref[23] && r[24] == ref[24] && r[25] == ref[25] &&
      r[26] == ref[26] && r[27] == ref[27] && r[28] == ref[28] &&
      r[29] == ref[29] && r[30] == ref[30] && r[31] == ref[31],
    "__builtin_ia32_pcmpgtb256 == native >");
  return 0;
}

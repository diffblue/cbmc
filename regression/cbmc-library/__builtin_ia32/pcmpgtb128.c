typedef char __gcc_v16qi __attribute__((__vector_size__(16)));
__gcc_v16qi __builtin_ia32_pcmpgtb128(__gcc_v16qi, __gcc_v16qi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native >) for all inputs.
  __gcc_v16qi a, b;
  __gcc_v16qi r = __builtin_ia32_pcmpgtb128(a, b);
  __gcc_v16qi ref = a > b;
  __CPROVER_assert(
    r[0] == ref[0] && r[1] == ref[1] && r[2] == ref[2] && r[3] == ref[3] &&
      r[4] == ref[4] && r[5] == ref[5] && r[6] == ref[6] && r[7] == ref[7] &&
      r[8] == ref[8] && r[9] == ref[9] && r[10] == ref[10] &&
      r[11] == ref[11] && r[12] == ref[12] && r[13] == ref[13] &&
      r[14] == ref[14] && r[15] == ref[15],
    "__builtin_ia32_pcmpgtb128 == native >");
  return 0;
}

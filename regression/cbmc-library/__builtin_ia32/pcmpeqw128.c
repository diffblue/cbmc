typedef short __gcc_v8hi __attribute__((__vector_size__(16)));
__gcc_v8hi __builtin_ia32_pcmpeqw128(__gcc_v8hi, __gcc_v8hi);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native ==) for all inputs.
  __gcc_v8hi a, b;
  __gcc_v8hi r = __builtin_ia32_pcmpeqw128(a, b);
  __gcc_v8hi ref = a == b;
  __CPROVER_assert(
    r[0] == ref[0] && r[1] == ref[1] && r[2] == ref[2] && r[3] == ref[3] &&
      r[4] == ref[4] && r[5] == ref[5] && r[6] == ref[6] && r[7] == ref[7],
    "__builtin_ia32_pcmpeqw128 == native ==");
  return 0;
}

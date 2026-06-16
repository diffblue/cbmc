typedef int __gcc_v8si __attribute__((__vector_size__(32)));
__gcc_v8si __builtin_ia32_pcmpgtd256(__gcc_v8si, __gcc_v8si);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native >) for all inputs.
  __gcc_v8si a, b;
  __gcc_v8si r = __builtin_ia32_pcmpgtd256(a, b);
  __gcc_v8si ref = a > b;
  __CPROVER_assert(
    r[0] == ref[0] && r[1] == ref[1] && r[2] == ref[2] && r[3] == ref[3] &&
      r[4] == ref[4] && r[5] == ref[5] && r[6] == ref[6] && r[7] == ref[7],
    "__builtin_ia32_pcmpgtd256 == native >");
  return 0;
}

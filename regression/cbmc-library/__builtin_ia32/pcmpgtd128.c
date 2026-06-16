typedef int __gcc_v4si __attribute__((__vector_size__(16)));
__gcc_v4si __builtin_ia32_pcmpgtd128(__gcc_v4si, __gcc_v4si);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native >) for all inputs.
  __gcc_v4si a, b;
  __gcc_v4si r = __builtin_ia32_pcmpgtd128(a, b);
  __gcc_v4si ref = a > b;
  __CPROVER_assert(
    r[0] == ref[0] && r[1] == ref[1] && r[2] == ref[2] && r[3] == ref[3],
    "__builtin_ia32_pcmpgtd128 == native >");
  return 0;
}

typedef long long __gcc_v2di __attribute__((__vector_size__(16)));
__gcc_v2di __builtin_ia32_pand128(__gcc_v2di, __gcc_v2di);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native &) for all inputs.
  __gcc_v2di a, b;
  __gcc_v2di r = __builtin_ia32_pand128(a, b);
  __gcc_v2di ref = a & b;
  __CPROVER_assert(
    r[0] == ref[0] && r[1] == ref[1], "__builtin_ia32_pand128 == native &");
  return 0;
}

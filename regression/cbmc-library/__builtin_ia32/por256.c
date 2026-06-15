typedef long long __gcc_v4di __attribute__((__vector_size__(32)));
__gcc_v4di __builtin_ia32_por256(__gcc_v4di, __gcc_v4di);

int main()
{
  // Exhaustive equivalence: the model must agree with CBMC's own
  // vector semantics (native |) for all inputs.
  __gcc_v4di a, b;
  __gcc_v4di r = __builtin_ia32_por256(a, b);
  __gcc_v4di ref = a | b;
  __CPROVER_assert(
    r[0] == ref[0] && r[1] == ref[1] && r[2] == ref[2] && r[3] == ref[3],
    "__builtin_ia32_por256 == native |");
  return 0;
}

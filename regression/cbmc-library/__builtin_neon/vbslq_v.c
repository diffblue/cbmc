// Generated model for the bitwise-select builtin (mnemonic BSL). The operation
// is bit-level, so it is independent of the lane type code: each result bit
// comes from a where the mask bit is set, otherwise from b.
typedef signed char v16 __attribute__((vector_size(16)));
typedef char v16qi __attribute__((vector_size(16)));

int main()
{
  v16 mask, a, b;
  v16 r = (v16)__builtin_neon_vbslq_v((v16qi)mask, (v16qi)a, (v16qi)b, 32);
  for(int i = 0; i < 16; i++)
    __CPROVER_assert(
      r[i] == (signed char)((mask[i] & a[i]) | (~mask[i] & b[i])),
      "vbslq selects bits by mask");
  return 0;
}

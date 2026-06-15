// Generated model for the saturating-add builtin (mnemonic SQADD); type code
// 32 selects the int8x16 interpretation. Check it against a clamped reference.
typedef signed char v16 __attribute__((vector_size(16)));
typedef char v16qi __attribute__((vector_size(16)));

int main()
{
  v16 a, b;
  v16 r = (v16)__builtin_neon_vqaddq_v((v16qi)a, (v16qi)b, 32);
  for(int i = 0; i < 16; i++)
  {
    int s = (int)a[i] + (int)b[i];
    int ref = s < -128 ? -128 : (s > 127 ? 127 : s);
    __CPROVER_assert(r[i] == ref, "vqaddq_s8 saturates");
  }
  return 0;
}

// Generated model for the halving-add builtin (mnemonic UHADD); type code 48
// selects the uint8x16 interpretation. Check it against floor((a+b)/2).
typedef unsigned char v16 __attribute__((vector_size(16)));
typedef char v16qi __attribute__((vector_size(16)));

int main()
{
  v16 a, b;
  v16 r = (v16)__builtin_neon_vhaddq_v((v16qi)a, (v16qi)b, 48);
  for(int i = 0; i < 16; i++)
    __CPROVER_assert(
      r[i] == (unsigned char)(((int)a[i] + (int)b[i]) >> 1),
      "vhaddq_u8 == floor((a+b)/2)");
  return 0;
}

// Generated model for the test-bits builtin (mnemonic CMTST); type code 32
// selects int8x16. Each lane is all-ones where (a & b) is non-zero.
typedef signed char v16 __attribute__((vector_size(16)));
typedef char v16qi __attribute__((vector_size(16)));

int main()
{
  v16 a, b;
  v16 r = (v16)__builtin_neon_vtstq_v((v16qi)a, (v16qi)b, 32);
  for(int i = 0; i < 16; i++)
    __CPROVER_assert(
      r[i] == ((a[i] & b[i]) != 0 ? -1 : 0), "vtstq_s8 sets lanes on bit test");
  return 0;
}

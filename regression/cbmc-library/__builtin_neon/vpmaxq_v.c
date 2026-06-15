// Generated model for the pairwise-maximum builtin (mnemonic SMAXP); type code
// 32 selects int8x16. The result is the pairwise maxima of a followed by those
// of b -- exercises the reshaping code path.
typedef signed char v16 __attribute__((vector_size(16)));
typedef char v16qi __attribute__((vector_size(16)));

int main()
{
  v16 a, b;
  v16 r = (v16)__builtin_neon_vpmaxq_v((v16qi)a, (v16qi)b, 32);
  for(int i = 0; i < 8; i++)
  {
    signed char ea = a[2 * i] > a[2 * i + 1] ? a[2 * i] : a[2 * i + 1];
    signed char eb = b[2 * i] > b[2 * i + 1] ? b[2 * i] : b[2 * i + 1];
    __CPROVER_assert(r[i] == ea, "vpmaxq_s8 lower half from a");
    __CPROVER_assert(r[8 + i] == eb, "vpmaxq_s8 upper half from b");
  }
  return 0;
}

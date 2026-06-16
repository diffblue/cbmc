// The NEON builtin is declared by the front-end (gcc_builtin_headers_aarch64.h)
// under an AArch64 target, and its body comes from the cprover library model in
// src/ansi-c/library/arm_neon.c.  The absolute difference of any vector with
// itself is zero, regardless of the lane interpretation (type code 32 = s8).
typedef char v16qi __attribute__((vector_size(16)));

int main()
{
  v16qi a;
  v16qi r = __builtin_neon_vabdq_v(a, a, 32);
  for(int i = 0; i < 16; i++)
    __CPROVER_assert(r[i] == 0, "vabdq of equal vectors is zero");
  return 0;
}

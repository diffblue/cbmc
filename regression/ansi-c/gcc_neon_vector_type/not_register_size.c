// As Clang does, only accept vectors of the size of a NEON register (64 or
// 128 bits): 3 lanes of int are 96 bits.
typedef __attribute__((neon_vector_type(3))) int bad_vector;

int main()
{
  bad_vector v;
  (void)v;
  return 0;
}

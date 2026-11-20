// Unlike neon_vector_type (a lane count), vector_size gives the size in bytes,
// which must be a multiple of the base type size. 3 is not a multiple of
// sizeof(int), so this must be rejected -- guarding the byte-size code path
// that the neon_vector_type lane-count handling shares.
typedef __attribute__((vector_size(3))) int bad_vector;

int main()
{
  bad_vector v;
  (void)v;
  return 0;
}

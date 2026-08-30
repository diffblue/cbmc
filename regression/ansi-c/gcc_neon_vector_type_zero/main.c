// neon_vector_type gives a lane count, which must be positive; a lane count of
// 0 must be rejected by the existing positivity check.
typedef __attribute__((neon_vector_type(0))) int bad_vector;

int main()
{
  bad_vector v;
  (void)v;
  return 0;
}

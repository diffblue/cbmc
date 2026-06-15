// A lane count of 0 must be rejected by the positivity check.
typedef __attribute__((neon_vector_type(0))) int bad_vector;

int main()
{
  bad_vector v;
  (void)v;
  return 0;
}

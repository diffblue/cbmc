int main()
{
  float x;
  __CPROVER_assume(x == 3.75f);
  __CPROVER_assert((int)x == 3, "int of positive");
  __CPROVER_assert((unsigned)x == 3u, "unsigned of positive");
  __CPROVER_assert((double)x == 3.75, "float to double");
  __CPROVER_assert((char)x == 3, "char of positive");
  __CPROVER_assert((_Bool)x, "bool of non-zero");

  float y;
  __CPROVER_assume(y == -2.5f);
  __CPROVER_assert((int)y == -2, "int of negative");
  __CPROVER_assert((long long)y == -2, "long long of negative");
  __CPROVER_assert((double)y == -2.5, "negative float to double");

  float z;
  __CPROVER_assume(0.0f <= z && z < 1000.0f);
  int iz = (int)z;
  __CPROVER_assert(iz >= 0 && iz < 1000, "range");
  __CPROVER_assert(iz != 999, "can be 999");
  return 0;
}

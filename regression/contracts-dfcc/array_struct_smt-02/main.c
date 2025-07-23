typedef struct
{
  int coeffs[1];
} mld_poly;

typedef struct
{
  mld_poly vec[1];
} mld_polyveck;

int main()
{
  mld_polyveck h;

  // clang-format off
  for(unsigned int i = 0; i < 1; ++i)
    __CPROVER_loop_invariant(i <= 1)
  {
    h.vec[i].coeffs[0] = 1;
  }
  // clang-format on

  return 0;
}

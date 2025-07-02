typedef struct
{
  int coeffs[2];
} mlk_poly;

// clang-format off
void mlk_poly_add(mlk_poly *r, const mlk_poly *b)
  __CPROVER_ensures(r->coeffs[0] == __CPROVER_old(*r).coeffs[0] + b->coeffs[0])
  __CPROVER_assigns(__CPROVER_object_upto(r, sizeof(mlk_poly)));
// clang-format on

int main()
{
  mlk_poly r[1];
  mlk_poly b[1];
  mlk_poly_add(&r[0], &b[0]);
}

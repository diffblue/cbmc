typedef __CPROVER_fixedbv[32][16] fixed;
typedef fixed fixedx2 __attribute__((vector_size(8)));

int main(void)
{
  fixedx2 v = {4, 2};
  fixedx2 r = v << 1;
  return 0;
}

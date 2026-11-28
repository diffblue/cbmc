// C11 6.7.5p6: an alignment specification of zero has no effect
_Alignas(0) int z1;
_Alignas(0) _Alignas(8) int z2;

struct Z3
{
  _Alignas(0) int m;
  char c;
};
_Static_assert(sizeof(struct Z3) == 2 * sizeof(int), "");
_Static_assert(_Alignof(struct Z3) == _Alignof(int), "");

int main(void)
{
  return 0;
}

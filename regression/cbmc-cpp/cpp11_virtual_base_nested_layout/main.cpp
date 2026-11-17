extern "C" void __CPROVER_assert(bool, const char *);
struct W
{
  int w;
};
struct V : virtual W
{
  int v;
};
struct B1 : virtual V
{
  int b1;
};
struct X
{
  int x;
};
struct B2 : virtual X
{
  int b2;
};
struct D : B1, B2
{
  int d;
};
int main()
{
  __CPROVER_assert(sizeof(V) == 16, "V: vptr v | w");
  __CPROVER_assert(sizeof(B1) == 32, "B1: vptr b1 | vptr v | w");
  __CPROVER_assert(sizeof(B2) == 16, "B2: vptr b2 | x");
  __CPROVER_assert(sizeof(D) == 56, "D: [vptr b1][vptr b2] d | vptr v | w | x");
  D o;
  __CPROVER_assert((char *)&o.b1 - (char *)&o == 8, "b1");
  __CPROVER_assert((char *)&o.b2 - (char *)&o == 24, "b2");
  __CPROVER_assert((char *)&o.d - (char *)&o == 28, "d");
  __CPROVER_assert((char *)&o.v - (char *)&o == 40, "v");
  __CPROVER_assert((char *)&o.w - (char *)&o == 44, "w");
  __CPROVER_assert((char *)&o.x - (char *)&o == 48, "x");
  return 0;
}

enum kind_t : int;
struct rec
{
  int a;
  kind_t k;
  int b;
};
struct outer
{
  rec r;
  int c;
};
rec g_r;
int get_b()
{
  return g_r.b;
}
int sum(outer o)
{
  return o.r.a + o.r.b + o.c + (int)o.r.k;
}

// An object tree that branches through many distinct struct types: each of
// the 20 types has two pointers to the next one, and only after 20 levels does
// a type recur, so max_nondet_tree_depth does not limit the 2^20 objects.
struct t0;
struct t1;
struct t2;
struct t3;
struct t4;
struct t5;
struct t6;
struct t7;
struct t8;
struct t9;
struct t10;
struct t11;
struct t12;
struct t13;
struct t14;
struct t15;
struct t16;
struct t17;
struct t18;
struct t19;
struct t0
{
  struct t1 *a, *b;
  int v;
};
struct t1
{
  struct t2 *a, *b;
  int v;
};
struct t2
{
  struct t3 *a, *b;
  int v;
};
struct t3
{
  struct t4 *a, *b;
  int v;
};
struct t4
{
  struct t5 *a, *b;
  int v;
};
struct t5
{
  struct t6 *a, *b;
  int v;
};
struct t6
{
  struct t7 *a, *b;
  int v;
};
struct t7
{
  struct t8 *a, *b;
  int v;
};
struct t8
{
  struct t9 *a, *b;
  int v;
};
struct t9
{
  struct t10 *a, *b;
  int v;
};
struct t10
{
  struct t11 *a, *b;
  int v;
};
struct t11
{
  struct t12 *a, *b;
  int v;
};
struct t12
{
  struct t13 *a, *b;
  int v;
};
struct t13
{
  struct t14 *a, *b;
  int v;
};
struct t14
{
  struct t15 *a, *b;
  int v;
};
struct t15
{
  struct t16 *a, *b;
  int v;
};
struct t16
{
  struct t17 *a, *b;
  int v;
};
struct t17
{
  struct t18 *a, *b;
  int v;
};
struct t18
{
  struct t19 *a, *b;
  int v;
};
struct t19
{
  struct t0 *a, *b;
  int v;
};
struct t0 *make(void);
int main(void)
{
  struct t0 *x = make();
  return x ? x->v : 0;
}

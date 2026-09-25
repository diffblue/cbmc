extern "C" void __CPROVER_assert(bool, const char *);
// A class with base classes was never padded (base-subobject layout was
// considered out of scope), so a bit-field run in the derived class was
// left incomplete: `struct D : B { int m : 28; short s; }' tripped
// size_of_expr_rec's "padding ensures offset at byte boundaries" invariant
// (crash) -- and the padding components flattened in from an already
// padded base made the derived class look "already padded" and clashed
// with the derived class's own padding names ($bit_field_padN).
struct B
{
  int x;
};
struct EB
{
};
struct D : public B
{
  int m : 28;
  unsigned short s;
};
struct D2 : public EB, public B
{
  int m : 28;
  unsigned short s;
};
struct P
{
  int a;
  short m : 13;
};
struct Q : public P
{
  short n : 3;
  struct
  {
    int q;
  } an;
};
struct R : public P
{
  short n : 3;
  unsigned long w : 45;
} __attribute__((packed));
int main()
{
  D d;
  d.x = 7;
  d.m = 3;
  d.s = 9;
  __CPROVER_assert(
    d.x == 7 && d.m == 3 && d.s == 9,
    "derived with bit-field then plain member");
  __CPROVER_assert(sizeof(D) == 12, "sizeof D");
  D2 e;
  e.x = 1;
  e.m = 2;
  e.s = 3;
  __CPROVER_assert(e.x == 1 && e.m == 2 && e.s == 3, "empty base too");
  Q q;
  q.a = 4;
  q.m = 5;
  q.n = 2;
  q.an.q = 6;
  __CPROVER_assert(
    q.a == 4 && q.m == 5 && q.n == 2 && q.an.q == 6,
    "padded base, derived bit-field, anonymous struct member");
  R r;
  r.a = 1;
  r.m = 2;
  r.n = 3;
  r.w = 4;
  __CPROVER_assert(
    r.a == 1 && r.m == 2 && r.n == 3 && r.w == 4, "packed derived");
  return 0;
}

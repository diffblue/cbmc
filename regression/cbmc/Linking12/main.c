// struct S is the same type in this translation unit, where struct Inner is
// complete, and in module.c, where it is incomplete (C11 6.2.7). The name of
// the anonymous union in struct S used to include the body of struct Inner, so
// it differed between the two files, and linking treated the two struct S as
// different types.

struct Inner
{
  int payload;
};

struct S
{
  union
  {
    struct Inner *via_struct;
    int *via_int;
  } u;
  int sentinel;
};

int points_to(struct S *p, struct Inner *inner);

int main(void)
{
  struct Inner inner = {7};
  struct S s;
  s.u.via_struct = &inner;
  s.sentinel = 42;
  __CPROVER_assert(points_to(&s, &inner), "member survived linking");
  return 0;
}

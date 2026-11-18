struct B
{
  int x;
};

struct S
{
  union
  {
    struct B *p;
    int *q;
  } u;
};

// struct S here is not compatible with the one in distinct_tags1.c, so the
// call from there has undefined behaviour; do not read through s
int get(struct S *s)
{
  return 7;
}

struct fatptr
{
  int *data;
  unsigned long int len;
};

struct slice
{
  int *data;
  unsigned long int len;
};

union repr {
  struct slice rust;
  struct fatptr raw;
};

struct slice cast(int *data, unsigned long int len)
{
  struct fatptr x;
  union repr z;
  x.data = data;
  x.len = len;
  z.raw = x;
  return z.rust;
}

struct fatptr cast2(int *data, unsigned long int len)
{
  struct slice w;
  union repr z;
  w.data = data;
  w.len = len;
  z.rust = w;
  return z.raw;
}

int main()
{
  int x = 256;

  struct slice z = cast(&x, 1);
  struct fatptr z2 = cast2(&x, 1);

  __CPROVER_assert(*z.data == 256, "test 1");
  __CPROVER_assert(*z2.data == 256, "test 2");
}

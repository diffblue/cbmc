struct holder
{
  union
  {
    long double ld;
    int i;
    const char *p;
  } v;
  int type;
};

static struct holder get(const struct holder *arr, unsigned k)
{
  struct holder h;
  h.type = arr[k].type;
  h.v = arr[k].v;
  return h;
}

static int read_int(const int *x)
{
  return *x;
}

int main()
{
  struct holder store[2];
  store[0].v.i = 42;
  store[0].type = 1;
  store[1].v.p = "x";
  store[1].type = 2;

  // copies of a union, by itself and as a member of a struct, read as a member
  // and through a pointer to the member's type
  struct holder a = get(store, 0);
  int out = read_int((const int *)&a);
  __CPROVER_assert(out == 42, "read through a pointer");
  __CPROVER_assert(a.v.i == 42, "read as a member");

  struct holder b = get(store, 1);
  const char *q = b.v.p;
  __CPROVER_assert(*q == 'x', "pointer member");

  // the value is a constant: the loop needs no unwinding assertion
  unsigned k = 0;
  for(int n = out; n > 0; --n)
    ++k;
  __CPROVER_assert(k == 42, "loop");

  __CPROVER_assert(0, "WRONG (must FAIL)");
  return 0;
}

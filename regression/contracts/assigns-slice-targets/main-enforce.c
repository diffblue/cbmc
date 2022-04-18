struct st
{
  int a;
  char arr1[10];
  int b;
  char arr2[10];
  int c;
};

void foo(struct st *s)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(s, sizeof(*s)))
  __CPROVER_assigns(__CPROVER_object_slice(s->arr1, 5))
  __CPROVER_assigns(__CPROVER_object_from(s->arr2 + 5))
// clang-format on
{
  // PASS
  s->arr1[0] = 0;
  s->arr1[1] = 0;
  s->arr1[2] = 0;
  s->arr1[3] = 0;
  s->arr1[4] = 0;

  // FAIL
  s->arr1[5] = 0;
  s->arr1[6] = 0;
  s->arr1[7] = 0;
  s->arr1[8] = 0;
  s->arr1[9] = 0;

  // FAIL
  s->arr2[0] = 0;
  s->arr2[1] = 0;
  s->arr2[2] = 0;
  s->arr2[3] = 0;
  s->arr2[4] = 0;

  // PASS
  s->arr2[5] = 0;
  s->arr2[6] = 0;
  s->arr2[7] = 0;
  s->arr2[8] = 0;
  s->arr2[9] = 0;
}

int main()
{
  struct st s;

  foo(&s);

  return 0;
}

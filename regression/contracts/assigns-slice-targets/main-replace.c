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
  s->arr1[0] = 0;
  s->arr1[1] = 0;
  s->arr1[2] = 0;
  s->arr1[3] = 0;
  s->arr1[4] = 0;

  s->arr2[5] = 0;
  s->arr2[6] = 0;
  s->arr2[7] = 0;
  s->arr2[8] = 0;
  s->arr2[9] = 0;
}

int main()
{
  struct st s;
  s.a = 0;
  s.arr1[0] = 0;
  s.arr1[1] = 0;
  s.arr1[2] = 0;
  s.arr1[3] = 0;
  s.arr1[4] = 0;
  s.arr1[5] = 0;
  s.arr1[6] = 0;
  s.arr1[7] = 0;
  s.arr1[8] = 0;
  s.arr1[9] = 0;

  s.arr2[0] = 0;
  s.arr2[1] = 0;
  s.arr2[2] = 0;
  s.arr2[3] = 0;
  s.arr2[4] = 0;
  s.arr2[5] = 0;
  s.arr2[6] = 0;
  s.arr2[7] = 0;
  s.arr2[8] = 0;
  s.arr2[9] = 0;
  s.c = 0;

  foo(&s);

  // PASS
  assert(s.a == 0);

  // FAIL
  assert(s.arr1[0] == 0);
  assert(s.arr1[1] == 0);
  assert(s.arr1[2] == 0);
  assert(s.arr1[3] == 0);
  assert(s.arr1[4] == 0);

  // PASS
  assert(s.arr1[5] == 0);
  assert(s.arr1[6] == 0);
  assert(s.arr1[7] == 0);
  assert(s.arr1[8] == 0);
  assert(s.arr1[9] == 0);

  // PASS
  assert(s.b == 0);

  // PASS
  assert(s.arr2[0] == 0);
  assert(s.arr2[1] == 0);
  assert(s.arr2[2] == 0);
  assert(s.arr2[3] == 0);
  assert(s.arr2[4] == 0);

  // FAIL
  assert(s.arr2[5] == 0);
  assert(s.arr2[6] == 0);
  assert(s.arr2[7] == 0);
  assert(s.arr2[8] == 0);
  assert(s.arr2[9] == 0);

  // PASS
  assert(s.c == 0);
  return 0;
}

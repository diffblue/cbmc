// Functions that DFCC does not instrument (here, through their `__VERIFIER`
// and `nondet` prefixes) and that write parts of objects. The loops must
// havoc those parts, but not the rest of the objects.
struct inner
{
  int x;
  int y;
};

struct S
{
  int a;
  int b;
  struct inner in;
  int arr[2];
};

struct S g;

// Writes a member of what its parameter points to.
void nondet_fill(struct S *s)
{
  s->a = 5;
}

// Writes a member of a global.
void __VERIFIER_global_member(void)
{
  g.a = 5;
}

// Writes a member of what its parameter points to.
void __VERIFIER_inner(struct inner *q)
{
  q->x = 5;
}

// Writes, through a callee, a member of a member of what its parameter
// points to.
void __VERIFIER_outer(struct S *p)
{
  __VERIFIER_inner(&p->in);
}

// Writes an element at a non-constant index of a member.
void __VERIFIER_element(struct S *p, int i)
{
  p->arr[i] = 5;
}

// Writes a member of an object after the one its parameter points to.
void __VERIFIER_next(struct S *p)
{
  p = p + 1;
  p->a = 5;
}

int main()
{
  struct S s = {0, 1, {0, 1}, {0, 0}};
  struct S t = {0, 1, {0, 1}, {0, 0}};
  struct S u = {0, 1, {0, 1}, {0, 0}};
  struct S v[2] = {{0, 1, {0, 1}, {0, 0}}, {0, 1, {0, 1}, {0, 0}}};
  g.b = 1;

  // The writes happen in a later iteration than the first, so that the
  // assertions after the loop only fail if the loop havocs their targets.
  for(int i = 0; i < 10; i++)
    // clang-format off
    __CPROVER_loop_invariant(0 <= i && i <= 10)
    // clang-format on
    {
      if(i == 5)
      {
        nondet_fill(&s);
        __VERIFIER_global_member();
        __VERIFIER_outer(&t);
        __VERIFIER_element(&u, 0);
        __VERIFIER_next(v);
      }
    }
  __CPROVER_assert(s.a == 0, "s.a written");
  __CPROVER_assert(s.b == 1, "s.b not written");
  __CPROVER_assert(g.a == 0, "g.a written");
  __CPROVER_assert(g.b == 1, "g.b not written");
  __CPROVER_assert(t.in.x == 0, "t.in.x written");
  __CPROVER_assert(t.a == 0, "t.a not written");
  __CPROVER_assert(u.arr[0] == 0, "u.arr[0] written");
  __CPROVER_assert(u.b == 1, "u.b not written");
  __CPROVER_assert(v[1].a == 0, "v[1].a written");
  return 0;
}

struct s
{
  int a;
  int b;
};

int get(int *q)
{
  return *q;
}

void set_a(struct s *p)
  // clang-format off
  __CPROVER_requires(__CPROVER_is_fresh(p, sizeof(*p)))
  __CPROVER_assigns(p->a)
// clang-format on
{
  // Taking the address of a local adds it to the set of locally allocated
  // objects of the write set, so that set is no longer empty when the
  // assignment to p->a is checked.
  int local = 1;
  p->a = get(&local);
}

int main()
{
  struct s *p;
  set_a(p);

  // a property for the solver to decide
  int y;
  __CPROVER_assume(y > 3);
  __CPROVER_assert(y != 2, "y is not 2");
  return 0;
}

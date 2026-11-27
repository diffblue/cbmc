struct S
{
  int a, b, c, d, e, f;
} s;

void h(void) __CPROVER_assigns(s.a, s.b, s.c, s.d, s.e, s.f)
{
  s.a = s.b = s.c = s.d = s.e = s.f = 0;
}

void foo(void) __CPROVER_assigns(s)
{
  h();
}

int main()
{
  foo();
  return 0;
}

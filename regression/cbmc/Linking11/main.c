// TU1: struct S with member 'x'
struct S
{
  int x;
};

// Function declared here, defined in module.c with a different struct S
int g(struct S *p);

int main()
{
  struct S s;
  s.x = 42;
  __CPROVER_assert(g(&s) == 42, "g returns s.x");
  return 0;
}

// This test exercises the Microsoft extension that allows flexible array
// members in unions by actually taking the address of the member and
// indexing into it, not just assigning to a sibling. This ensures the
// zero-length encoding produced by the type-checker survives downstream
// processing.

union U
{
  int n;
  char flexible_array_member[];
};

int main()
{
  union U u;
  u.n = 42;
  char *p = &u.flexible_array_member[0];
  (void)p;
}

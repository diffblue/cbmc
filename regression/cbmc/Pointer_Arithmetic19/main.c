struct S
{
  int *p;
  int s;
};

union U {
  struct S st;
  int i;
};

int main()
{
  int x;
  int *ip = &x;

  union U u;
  u.st.p = ip;
  u.st.s = 1;

  int A[2] = {42, 43};
  // the following should behave the same as "int *p = A + u.st.s;"
  int *p = u.st.s + A;
  assert(*p == 43);
}

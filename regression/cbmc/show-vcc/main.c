int main()
{
  __CPROVER_bool a, b, c, d;
  __CPROVER_assume(a);
  __CPROVER_assume(b);
  __CPROVER_assert(c || d, "some property");
}

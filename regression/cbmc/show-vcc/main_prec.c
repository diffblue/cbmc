int main()
{
  __CPROVER_bool a, b, c;
  int x, y, z;
  x = y + z;
  a = (b == c);
  __CPROVER_assert(0, "some property");
}

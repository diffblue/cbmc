int x;

int bar(int bar_a)
{
  x = 2;
  x++;
  __CPROVER_assert(0, "assertion");
}

int main()
{
  x = 1;
  bar(0);
}

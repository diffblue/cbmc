int main()
{
  _Bool a;
  int x;

  if(a)
    x = 1;
  else
    x = 1;
  __CPROVER_assert(x > 0, "");
}

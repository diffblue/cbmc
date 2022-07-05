int main()
{
  int s;

  int i = 0;
  if(i != s)
    ++i;
  else
    __CPROVER_assert(s == 0, "constant propagate");

  int s2 = s;
}

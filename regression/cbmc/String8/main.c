int main()
{
  _Bool branch = __VERIFIER_nondet__Bool();
  const char *str = 0;

  if(branch)
  {
    str = "foo";
  }
  else
  {
    str = "bar";
  }

  char a = str[2];
  __CPROVER_assert(a == 'o' || a == 'r', "");

  return 0;
}

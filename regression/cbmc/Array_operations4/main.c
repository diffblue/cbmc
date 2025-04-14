int main()
{
  char source[8];
  int int_source[2];
  int target[4];
  int n;
  if(n >= 0 && n < 3)
  {
    __CPROVER_array_replace(&target[n], source);
    __CPROVER_array_replace(&target[n], int_source);
    __CPROVER_assert(target[n] == int_source[0], "");
    __CPROVER_assert(target[n + 1] == int_source[1], "");
  }
}

int main()
{
  // __builtin_scanf takes a format string and then any number of arguments
  __builtin_scanf("x");
  int x;
  __builtin_scanf("%d", &x);
  return 0;
}

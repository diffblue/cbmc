// C++17 if/switch with initializer
int main()
{
  if(int x = 42; x > 0)
  {
    __CPROVER_assert(x == 42, "if init");
  }

  switch(int y = 1; y)
  {
  case 1:
    __CPROVER_assert(y == 1, "switch init");
    break;
  default:
    break;
  }

  return 0;
}

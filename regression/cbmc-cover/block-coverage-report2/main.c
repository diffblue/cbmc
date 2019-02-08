// This is supposed to be testing basic blocks with inlining,
// but cbmc has now turned off inlining by default.

inline int foo(int x)
{
  int y;
  y = x + 1;
  return y;
}

main()
{
  int x;
  x = 10;
  while(x)
  {
    int y;
    y = foo(x);
    if(y < 5)
      break;
    x--;
  }

  return;
}

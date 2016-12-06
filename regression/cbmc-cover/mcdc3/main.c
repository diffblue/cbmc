int main()
{
  unsigned x, y;

  __CPROVER_input("x", x);
  __CPROVER_input("y", y);

  if (!(x>3) && y<5)
    ;

  return 1;
}

int main()
{
  unsigned x;

  __CPROVER_input("x", x);

  if(x<3)
    ;

  return 1;
}

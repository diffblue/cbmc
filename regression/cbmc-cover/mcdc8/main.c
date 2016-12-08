int main()
{
  _Bool a, b, c;

  __CPROVER_input("a", a);
  __CPROVER_input("b", b);
  __CPROVER_input("c", c);

  if ( (a || b) && c )
  {
  /* instructions */
  }
  else
  {
  /* instructions */
  }

  return 1;
}

void foo(int i)
{
  // We use integer constants that we grep for later in a goto program.
  int x = 1001 + i;
  if(i > 0)
  { //foo.coverage.2
    x = 1002 + i;
    x = 1003 + i;
  }
  else
    x = 1004 + i;
  x = 1005 + i;
}

int foo(int x)
{
  return x;
}

int main()
{
  int m, n;

#pragma CPROVER check push
#pragma CPROVER check enable "signed-overflow"
  // generate assertions for the following statements
  int x = m = n + n;
  ++n;
  n++;
  n += 1;
  foo(x + n);
#pragma CPROVER check pop
  // but do not generate assertions for these
  x = n + n;
  foo(x + n);
  return x;
}

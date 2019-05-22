int foo(int x)
{
  return x;
}

int main()
{
  int m, n;

#pragma CPROVER check push
#pragma CPROVER check disable "signed-overflow"
  // do not generate assertions for the following statements
  int x = m = n + n;
  ++n;
  n++;
  n += 1;
  foo(x + n);
  // pop all annotations
#pragma CPROVER check pop
  // but do generate assertions for these
  x = n + n;
  foo(x + n);
  return x;
}

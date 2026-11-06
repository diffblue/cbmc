struct S
{
  int f;
} s;
int main()
{
  struct S *q = &s;
  int x = 0;
  s.f = 0;
  if(q->f == 0)
  {
    s.f = 1;
    x = 2;
  }
  __CPROVER_assert(x == 2, "x set");
  return 0;
}

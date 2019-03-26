struct S
{
  struct S *s;
  struct S *a[2];
};

int main()
{
  struct S s;
  s.s = 0;
  return 0;
}

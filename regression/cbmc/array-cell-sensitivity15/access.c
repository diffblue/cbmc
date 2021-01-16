struct st
{
  char c;
  int n[4];
};

int main()
{
  unsigned i;
  int k;
  i %= 4;
  struct st s;
  int *p = s.n;
  p[i] = k;
  return 0;
}

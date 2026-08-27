// file-local count with the same name as the one in unwind_a.c; after linking
// its loop is renamed and identified as count$link1.0
static int count(int n)
{
  int s = 0;
  for(int i = 0; i < n; i++)
    s += 2;
  return s;
}

int b_entry(int n)
{
  return count(n);
}

// file-local count; its loop is identified as count.0 after linking
static int count(int n)
{
  int s = 0;
  for(int i = 0; i < n; i++)
    s += 1;
  return s;
}

int a_entry(int n)
{
  return count(n);
}

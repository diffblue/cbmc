int main()
{
  int n, *m;
  __atomic_fetch_add(n, m, 0);
  return 0;
}

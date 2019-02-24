int main()
{
  int n, *m;
  __atomic_add_fetch(n, m, 0);
  return 0;
}

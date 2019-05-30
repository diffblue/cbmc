int main()
{
  int n, *m, *o;
  __sync_bool_compare_and_swap(n, m, o);
  return 0;
}

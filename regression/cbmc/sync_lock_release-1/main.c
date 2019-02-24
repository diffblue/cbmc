int main()
{
  int *n;
  __sync_lock_release(n);
  return 0;
}

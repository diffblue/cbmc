int main()
{
  void *ptr;
  if(ptr == 0)
  {
    return 0;
  }
  __CPROVER_assert(ptr != 0, "null");
}

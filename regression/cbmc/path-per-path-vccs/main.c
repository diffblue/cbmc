int main()
{
  __CPROVER_assert(0, "");
  int x;
  while(x)
    --x;
}

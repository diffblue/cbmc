int main()
{
  int x;
for_loop:
  for(int i = 0; i < x; ++i)
    --x;
  for(int j = 0; j < 5; ++j)
    ++x;
  __CPROVER_assert(0, "can be reached");
}

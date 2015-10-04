int main(void)
{
  int x = 0;
  while (x < 2)
  {
    int condition;
    if(condition)
      ++x;
    ++x;
  }
  __CPROVER_assert(x == 2, "A");
  return 0;
}

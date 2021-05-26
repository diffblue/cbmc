int main()
{
  int x = 0;
  if(nondet())
  {
    x = 30;
  }

  if(x < 10)
  {
    assert(x < 20);
  }
}

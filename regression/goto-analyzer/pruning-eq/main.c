int main()
{
  int x = 0;
  if(nondet())
  {
    x = 30;
  }

  if(x == 30)
  {
    assert(x == 20);
    assert(x == 30);
  }
}

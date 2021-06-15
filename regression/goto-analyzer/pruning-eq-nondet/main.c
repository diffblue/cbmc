int main()
{
  int x = nondet();

  if(x == 30)
  {
    assert(x == 20);
    assert(x == 30);
  }
  else
  {
    assert(x != 30);
  }
}

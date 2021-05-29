int main()
{
  int x = nondet();

  if(x < 10)
  {
    assert(x < 20);
  }
}

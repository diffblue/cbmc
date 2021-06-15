int main()
{
  int x = nondet();

  if(10 < x)
  {
    assert(5 < x);
  }
}

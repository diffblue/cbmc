_Bool nondet_bool();
int main()
{
  int x = 0;
  while(1)
  {
    if(nondet_bool())
      x = x + 1;
    assert(x != 1000);
  }
}

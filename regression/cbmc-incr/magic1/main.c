void loop(int y)
{
  int x;
  __CPROVER_assume(x==0);
  while(x<y) {
    x=x+1;
    assert(x<=y);
  }
}

int main()
{
  loop(1);
  loop(2);
  loop(6);
  loop(12);
  loop(17);
  loop(21);
  loop(40);
  loop(60);
}

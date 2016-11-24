struct x
{
  int *q;
  
  x();
};

x::x():q(0)
{
}

int main()
{
  x a;
  assert(a.q==0);
}

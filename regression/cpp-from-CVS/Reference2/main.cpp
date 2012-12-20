int g;

class X
{
};

int &function()
{
  return g;
}

int main()
{
  g=1;
  function()=2;
  assert(g==2);

  {  
    int *p=&g;
    int &r=*p;
    assert(r==2);
  }
  
  {
    X x;
    X *p=&x;
    X &r=*p;
  }
}

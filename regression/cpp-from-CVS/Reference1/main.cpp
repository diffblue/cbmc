int g;

void function(int &ref)
{
  ref=2;
}

int main()
{
  int &r=g;
  
  r=1;
  
  assert(g==1);
  
  function(r);
  
  assert(g==2);
  
  // ?: does produce an l-value, apparently
  int &s=g?r:g;
}

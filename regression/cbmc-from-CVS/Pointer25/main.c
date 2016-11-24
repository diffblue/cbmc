int main()
{
  int x;
  void *p;

  // from integer 0 to NULL
  
  if(x==0)
  {
    p=x;
    assert(p==0);
  }
  
  // the other way around
  
  if(p==0)
  {
    x=p;
    assert(x==0);
  }
}

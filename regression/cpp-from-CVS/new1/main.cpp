void single_object()
{
  int *p;
  
  p=new int(2);

  assert(*p==2);
  
  delete p;
}

void array()
{
  int *q;
  
  q=new int[100];
  
  q[50]=1;
  
  // _must_ use delete[] here
  delete[] q;
}

int main()
{
  single_object();
  array();
  return 0;
}

int test;

int main()
{
  test=0;
  test=~test;
  assert(test==-1);
  
  test=0;
  test=!test;
  assert(test==1);
  
  test=100;
  test=!test;
  assert(test==0);

  assert(!!100==1);
}

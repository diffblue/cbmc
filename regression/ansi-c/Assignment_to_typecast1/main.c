int main()
{
  int i;

  // gcc warns that this will go
  // away in the future (hopefully!)
  (int)i|=2;
  (unsigned int)i|=2;

  void *p;
  
  (int *)p+=1;
}

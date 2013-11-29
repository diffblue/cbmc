void main()
{
  int x;
  char * cp = &x;

  for (int i=0; i!= sizeof(int); i++)
    *(cp+i) = 0;

  // should work with any endianness
  assert(x==0); 
}


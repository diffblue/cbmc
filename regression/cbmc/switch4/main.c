main()
{
  int x;

  switch(x)
  {
  case 0:
    goto end;
    
  default:
    x = 0;
  }

 end:
  assert(x==0);
}

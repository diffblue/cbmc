int main(int argc, char* argv[])
{
  if(argc>2)
  {
    argc=1;
  }
  else
  {
    argc=2;
  }

  switch(argc)
  {
    case 0:
      argc=3;
      break;
    case 1:
      argc=2;
      break;
  }

  return 0;
}

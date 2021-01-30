int unknown();

int main(int argc, char argv[])
{
  int p;
  int q;

  if(unknown())
  {
    p = 2;
    q = 5;
  }
  else
  {
    p = 3;
    q = 10;
  }

  int t = p + q;
}

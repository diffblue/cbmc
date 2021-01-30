int unknown();

int main(int argc, char argv[])
{
  int p = 2;
  int q = 3;

  if(unknown())
    p += 2;
  else
    p += 3;

  int t = p + q;
}

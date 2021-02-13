int unknown();

int main(int argc, char argv[])
{
  int p = 2;

  if(unknown())
    p += 2;
  else
    p += 3;
}

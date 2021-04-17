int unknown();

int main()
{
  int i = 0;
  int p = 0;

  if(unknown())
    p = 5;
  if(unknown())
    p = 10;

  if(p >= 5)
    i = 5;
  else
    i = -5;
}

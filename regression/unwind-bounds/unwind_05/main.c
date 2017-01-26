
int main()
{
  int i;
  int j;

  i = 0;
  while(i < 3) // main.1: 3
  {
    i++;
    i += 3;
    for(j = 0; j < 4; j++) {} // main.0: 4
    i -= 3;
  }

  i = 0;
  while(i != 7) // main.2: 1
  {
    i = 7;
  }
}


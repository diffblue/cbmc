
int x;

int main()
{
  int i;

  for (i = 0; i < 4; i++) // main.0: 4
  {
    continue;
    i--;
  }

  for (i = 0; i < 3; i++) // main.1: 3
  {
    x = 1;
    if (x) {
      x = 2;
      continue;
      x = 3;
    }
    x = 4;
  }

  for (i = 0; i < 7; i++) // main.2: 7
  {
    if(x) {
      continue;
    }
  }

  i = 0;
  while (i < 5) // main.3: 5
  {
    i++;
    continue;
  }

  i = 0;
  do {
    i++;
    continue;
    i--;
    x = 17;
  } while (i < 2); // main.4: 2
}


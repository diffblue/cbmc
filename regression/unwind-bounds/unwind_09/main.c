
int x;
int y;

int main()
{
  int i;

  for (i = 0; i < 4; i++) // main.0: 1
  {
    x = 1;
    break; // unconditional break
  }

  for (i = 0; i < 3; i++) // main.1: 3
  {
    x = 1;
    if(y) {
      x = 2;
      break; // conditional break
      x = 3;
    }
    x = 4;
  }

  for(i = 0; i < 7; i++) // main.2: 7
  {
    if(y) {
      break; // conditional break
    }
  }
}



int x;

int main()
{
  int i;
  int j;

  for(i = 0; i < 3; i++) { // main.1: 3

    if (x > 3)
    {
      x = 5;
    }

    if (x < 12) {
      for(j = 0; j < i; j++) {} // main.0: 2
    }

    j = 7;
  }
}


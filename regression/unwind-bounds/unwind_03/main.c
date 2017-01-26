
int main()
{
  int i;
  int j;

  for(i = 0; i < 3; i++) { // main.1: 3
    for(j = 0; j < 7; j++) {} // main.0: 7
  }

  int k;

  for(i = 0; i < 2; i++) { // main.4: 2
    for(j = 0; j < 8; j++) { // main.3: 8
      for(k = 0; k < 9; k++) {} // main.2: 9
    }
  }
}


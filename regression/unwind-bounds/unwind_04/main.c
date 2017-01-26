
int main()
{
  int i;
  int j;

  for(i = 0; i < 3; i++) { // main.1: 3
    for(j = 0; j < i; j++) {} // main.0: 2
  }

  int k;

  for(i = 0; i < 2; i++) { // main.4: 2
    for(j = 0; j < i; j++) { // main.3: 1
      for(k = 0; k < j; k++) {} // main.2: 0
    }
  }
}


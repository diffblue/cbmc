
int x;

int main()
{
  int i;

  i = 0;
  do {
    i++;
  } while (i < 3); // main.0: 3

  i = 0;
  do {
    if(x) {
       i++;
     } else {
       i++;
     }
  } while (i < 4); // main.1: 4

  i = 0;
  do {
    int j;
    i++;
    for (j = 0; j < 7; j++) {} // main.2: 7
  } while (i < 5); // main.3: 5

  i = 0;
  do {
    int j;
    j = 0;
    do {
      j++;
    } while (j < 2); // main.4: 2
    i++;
  } while (i < 2); // main.5: 2
}


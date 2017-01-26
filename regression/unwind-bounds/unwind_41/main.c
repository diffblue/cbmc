
int a[3];

void func(void)
{
  int i;

  do { // func.2: 1
    do {} while(0); // func.0: 1

  for (i=0; i<3; i++) // func.1: 3
    a[i] = 0;
  }
  while(0);
}

int main()
{
  func();
  return 0;
}


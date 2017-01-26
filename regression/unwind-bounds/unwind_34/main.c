
int main()
{
  int i;
  for (i = 0; i < 200; i++) {}

  i = 0;
  while (i < 10) {
    L:
    i++;
  }

  goto L;

  for(i = 0; i < 7; i++) {}
  for(i = 0; i < 5; i++) {}

  return 0;
}


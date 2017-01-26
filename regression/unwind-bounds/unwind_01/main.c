
int main()
{
  int i;

  for(i = 0; i < 10; i++) {} // 10

  for(i = 5; i < 10; i++) {} // 5

  for(i = 0; i < 10;) { i++; } // 10

  for(i = 0; i <= 10; i++) {} // 11
}


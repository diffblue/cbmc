int globalX;

void f00()
{
}

int main()
{
  globalX = 1;

  f00();

  assert(globalX == 1);

  globalX = 2;

  f00();

  assert(globalX == 2);

  return 0;
}

typedef int CODETYPE (int a);

extern CODETYPE func;

int func(int a)
{
  return 1;
}

int main(void)
{
  return func(2);
}

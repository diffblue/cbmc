typedef struct
{
  unsigned char array[4];
} A;

void func(A *ptr)
{
  int i = 1;
  assert(ptr[i].array[0] == 2);
}

int main()
{
  A a[2];
  a[1].array[0] = 2;
  func(a);
  return 0;
}

void f(int, int array[*][*]);

void f(int size, int array[size][size])
{
  assert(sizeof(array)==sizeof(int *));
  assert(sizeof(*array)==sizeof(int)*1000);
}

int main()
{
  f(1000, 0);
}

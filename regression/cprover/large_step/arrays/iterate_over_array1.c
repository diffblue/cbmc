int array[10];

int main()
{
  for(__CPROVER_size_t i = 0; i < sizeof(array) / sizeof(int); i++)
    array[i] = 0;
}

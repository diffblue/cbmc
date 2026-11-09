int array[100];

int main()
{
  unsigned long int index;

  // safe owing to shortcircuit semantics
  if(index < 100 && array[index] != 123)
  {
  }
}

int array[] = {'a', 'b', 'c', 'd', 'e', 'f'};

int main()
{
  int i;
  if(i >= 0 && i <= 5)
    __CPROVER_assert(array[i] == 'a' + i, "property 1"); // passes
}

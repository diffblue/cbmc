// constant array of non-constant integers
typedef int array_type[10];
const array_type array = {1, 2, 3};

int main()
{
  // should fail
  array[1] = 2;
}

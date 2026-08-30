int array[100];

int main()
{
  int *p = array;
  int x = p[10];  // safe
  int y = p[100]; // unsafe
  int z = p[-1];  // unsafe
}

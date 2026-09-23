int array[100];

int main()
{
  int x = array[10];  // safe
  int y = array[100]; // unsafe
  int z = array[-1];  // unsafe
}

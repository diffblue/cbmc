int unknown();

int main()
{
  int array[2] = {1, 2};
  int p;

  if(unknown())
    p = 0;
  else
    p = 1;
  if(unknown())
    array[0] = 3;

  int t = array[p];
}

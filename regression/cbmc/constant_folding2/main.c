typedef struct _pair
{
  int x;
  int y;
} pair;

int main (void)
{
  pair p;
  p.x = 0.0;
  p.y = (int)0.0f;
  
  int array[2];
  array[0] = 0;
  array[1] = (int)0.0f;
  
  int i=0;
  
  while (i < p.x) i++;
  while (i < array[0]) i++;

  return 0;
}

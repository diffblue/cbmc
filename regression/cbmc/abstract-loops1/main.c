#define ROW 10
#define COL 10

void main()
{
  int sum;
  int image[ROW][COL];

  // shrinkable
  for(int j = 0; j < COL; j++)
    image[0][j] = 0;

  sum = 0;
  // outer loop unshrinkable
  // inner loop shrinkable
  for(int i = 0; i < ROW; i++)
  {
    image[i][0] = 0;
    sum = sum + i;
    for(int j = 0; j < COL; j++)
      image[sum][j] = 0;
  }
}

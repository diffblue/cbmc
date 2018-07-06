#define ROW 3
#define COL 10

void boo(int r)
{
  int val = 0;
  int image[ROW][COL];
  ;
  // shrinkable, and set as shrink target
  for(int j = 0; j < COL; j++)
  {
    int c = j + val;
    image[r][c] = val;
  }
}

void main()
{
  int r;
  int buffer[ROW];
  // not shrinkable since r is used in mem-safe assertion in boo()
  // and r update itself in loop
  for(int i = 0; i < ROW; i++)
  {
    r = r + i;
    boo(r);
    buffer[i];
  }

  // shrinkable
  for(int i = 0; i < ROW; i++)
  {
    boo(i);
    buffer[i];
  }
}

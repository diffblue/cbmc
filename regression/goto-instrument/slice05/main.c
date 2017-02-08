int main()
{
  int x = 1; /* considering changing this line */
  int y = 3;
  int p = x + y;
  int z = y -2;
  int r = 0;

  if(p==0)
  r++;

  assert(r==0);

  return 0;
}

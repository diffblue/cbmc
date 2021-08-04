struct cartesian_coorindate
{
  int x;
  int y;
};

int main()
{
  struct cartesian_coorindate u;
  struct cartesian_coorindate *p = &u;
  p->x;
  p->y;
  p->x++;
  p->y--;
}

int nondet(void);
int nondet_bool(void);

struct cartesian_coorindate
{
  int x;
  int y;
};

int main()
{
  struct cartesian_coorindate u = {nondet(), nondet()};
  if(nondet_bool())
  {
    u.x++;
    u.y--;
  }
  else
  {
    u.x += 6;
    u.y -= 6;
  }

  return 0;
}

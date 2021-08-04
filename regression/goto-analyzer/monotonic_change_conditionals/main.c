int nondet_bool(void);

int main()
{
  int x;
  if(nondet_bool())
    x++;
  else
    x += 6;

  int y;
  if(nondet_bool())
    y++;
  else
    y -= 6;

  return 0;
}

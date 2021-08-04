int nondet_bool(void);

int main()
{
  int x = 42;
  if(nondet_bool())
    x++;
  else
    x += 6;

  int y = 42;
  if(nondet_bool())
    y++;
  else
    y -= 6;

  return 0;
}

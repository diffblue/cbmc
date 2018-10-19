enum Colour
{
  PINK,
  RED,
  BLUE
};

void do_red()
{
  int a1;
  int a2;
  int a3;
  int a4;
  int a5;
  int a6;
  int a7;
  int a8;
  int a9;
  int a10;
  int a11;
  int a12;
  int a13;
  int a14;
  int a15;
  int a16;
  int a17;
  int a18;
  int a19;
  int a20;
}

void do_blue()
{
  int a1;
  int a2;
  int a3;
  int a4;
  int a5;
  int a6;
  int a7;
  int a8;
  int a9;
  int a10;
  int a11;
  int a12;
  int a13;
  int a14;
  int a15;
  int a16;
  int a17;
  int a18;
  int a19;
  int a20;
}

void do_pink()
{
  int a1;
  int a2;
  int a3;
  int a4;
  int a5;
  int a6;
  int a7;
  int a8;
  int a9;
  int a10;
  int a11;
  int a12;
  int a13;
  int a14;
  int a15;
  int a16;
  int a17;
  int a18;
  int a19;
  int a20;
}

enum Colour pop()
{
  int x, y;
  if(x)
    return PINK;
  else if(y)
    return RED;
  else
    return BLUE;
}

/* The branches of this function are less disjoint from each other than
 * the branches of the switch-statement in dispatch(), because they call
 * common code.
 */
void not_dispatch()
{
  while(1)
  {
    switch(pop())
    {
    case PINK:
    {
      do_pink();
      do_red();
      break;
    }
    case RED:
    {
      do_red();
      do_blue();
      break;
    }
    case BLUE:
    {
      do_blue();
      do_pink();
      break;
    }
    }
  }
}

void dispatch()
{
  while(1)
  {
    switch(pop())
    {
    case PINK:
    {
      do_pink();
      break;
    }
    case RED:
    {
      do_red();
      break;
    }
    case BLUE:
    {
      do_blue();
      break;
    }
    }
  }
}

int main()
{
  dispatch();
  not_dispatch();
  return 0;
}

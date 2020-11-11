#include <assert.h>

struct my_struct
{
  int i;
  double d;
  char str[2];
};

int main(void)
{
  int nondet_choice, nondet_choice2;

  struct my_struct s;

  if(nondet_choice)
    s.d = 1.0;
  else
    s.d = 2.0;

  if(nondet_choice)
  {
    s.str[0] = 'x';
    s.str[1] = '\n';
  }
  else
  {
    s.str[0] = 'y';
    s.str[1] = '\n';
  }

  struct my_struct s_show = s;

  assert(s.i == 0);

  assert(s.d == 1.0);
  assert(s.d == 1.0 || s.d == 2.0);
  assert(s.d > 0.0);
  assert(s.d > 10.0);

  assert(s.str[0] == 'x');
  assert(s.str[0] == 'x' || s.str[0] == 'y');
  assert(s.str[1] == '\n');

  struct my_struct t = {1, 3.0, {'z', '\n'}};
  struct my_struct u;

  if(nondet_choice2)
    u = s;
  else
    u = t;

  struct my_struct u_show = u;

  assert(u.i == 1);

  assert(u.d == 3.0);
  assert(u.d == 1.0 || u.d == 2.0 || u.d == 3.0);
  assert(u.d > 0.0);
  assert(u.d > 10.0);

  assert(u.str[0] == 'z');
  assert(u.str[0] == 'x' || u.str[0] == 'y' || u.str[0] == 'z');
  assert(u.str[1] == '\n');

  return 0;
}

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

  __CPROVER_assert(s.i == 0, "assertion s.i == 0");

  __CPROVER_assert(s.d == 1.0, "assertion s.d == 1.0");
  __CPROVER_assert(
    s.d == 1.0 || s.d == 2.0, "assertion s.d == 1.0 || s.d == 2.0");
  __CPROVER_assert(s.d > 0.0, "assertion s.d > 0.0");
  __CPROVER_assert(s.d > 10.0, "assertion s.d > 10.0");

  __CPROVER_assert(s.str[0] == 'x', "assertion s.str[0] == 'x'");
  __CPROVER_assert(
    s.str[0] == 'x' || s.str[0] == 'y',
    "assertion s.str[0] == 'x' || s.str[0] == 'y'");
  __CPROVER_assert(s.str[1] == '\n', "assertion s.str[1] == '\n'");

  struct my_struct t = {1, 3.0, {'z', '\n'}};
  struct my_struct u;

  if(nondet_choice2)
    u = s;
  else
    u = t;

  struct my_struct u_show = u;

  __CPROVER_assert(u.i == 1, "assertion u.i == 1");

  __CPROVER_assert(u.d == 3.0, "assertion u.d == 3.0");
  __CPROVER_assert(
    u.d == 1.0 || u.d == 2.0 || u.d == 3.0,
    "assertion u.d == 1.0 || u.d == 2.0 || u.d == 3.0");
  __CPROVER_assert(u.d > 0.0, "assertion u.d > 0.0");
  __CPROVER_assert(u.d > 10.0, "assertion u.d > 10.0");

  __CPROVER_assert(u.str[0] == 'z', "assertion u.str[0] == 'z'");
  __CPROVER_assert(
    u.str[0] == 'x' || u.str[0] == 'y' || u.str[0] == 'z',
    "assertion u.str[0] == 'x' || u.str[0] == 'y' || u.str[0] == 'z'");
  __CPROVER_assert(u.str[1] == '\n', "assertion u.str[1] == '\n'");

  return 0;
}

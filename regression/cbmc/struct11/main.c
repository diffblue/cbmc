#include <assert.h>

struct prefix
{
  int integer;
  int *p;
};

struct full_struct
{
  int integer;
  int *p;
  int something_else;
};

void full_to_prefix()
{
  int some_int=1;
  struct full_struct f_s;
  f_s.integer=10;
  f_s.p=&some_int;
  struct prefix *prefix_p=(struct prefix *)&f_s;
  assert(prefix_p->integer==10);
  assert(*prefix_p->p==1);
}

void prefix_to_full()
{
  int some_int=1;
  struct prefix prefix;
  prefix.integer=10;
  prefix.p=&some_int;
  struct full_struct *f_s_p=(struct full_struct *)&prefix;
  assert(f_s_p->integer==10);
  assert(*f_s_p->p==1);
}

int main()
{
  full_to_prefix();
  prefix_to_full();
}

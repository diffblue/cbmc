int global_int = 0;
int global_int_show = 0;

int main(void)
{
  int nondet_choice;

  if(nondet_choice)
    global_int = 1;
  else
    global_int = 2;
  global_int_show = global_int;

  __CPROVER_assert(global_int == 2, "assertion global_int == 2");
  __CPROVER_assert(
    global_int == 1 || global_int == 2,
    "assertion global_int == 1 || global_int == 2");
  __CPROVER_assert(global_int > 0, "assertion global_int > 0");
  __CPROVER_assert(global_int > 3, "assertion global_int > 3");

  double local_double;

  if(nondet_choice)
    local_double = 1.0;
  else
    local_double = 2.0;
  double local_double_show = local_double;

  __CPROVER_assert(local_double == 2.0, "assertion local_double == 2.0");
  __CPROVER_assert(
    local_double == 1.0 || local_double == 2.0,
    "assertion local_double == 1.0 || local_double == 2.0");
  __CPROVER_assert(local_double > 0.0, "assertion local_double > 0.0");
  __CPROVER_assert(local_double > 3.0, "assertion local_double > 3.0");

  double d1 = 1.0;
  double d2 = 2.0;
  double *local_double_ptr;

  if(nondet_choice)
    local_double_ptr = &d1;
  else
    local_double_ptr = &d2;
  double *local_double_ptr_show = local_double_ptr;

  __CPROVER_assert(
    local_double_ptr == &d2, "assertion local_double_ptr == &d2");
  __CPROVER_assert(
    local_double_ptr == &d1 || local_double == &d2,
    "assertion local_double_ptr == &d1 || local_double == &d2");
  __CPROVER_assert(
    *local_double_ptr > 0.0, "assertion *local_double_ptr > 0.0");
  __CPROVER_assert(
    *local_double_ptr > 3.0, "assertion *local_double_ptr > 3.0");

  return 0;
}

#include <assert.h>

static void noop()
{
}

int test(int nondet_int_array[])
{
  int a = 1, b = 2, c = 3;
  int *ptr_to_a = &a, *ptr_to_b = &b, *ptr_to_c = &c, *ptr_to_null = 0;

  // Symex knows the value of ptr_to_a, ptr_to_b, ptr_to_c and ptr_to_null, so
  // it should be able to evaluate simple conditions involving them.

  // Equality "=="

  // A non-null pointer and a matching value
  int unconditionally_reachable_1;
  if(ptr_to_a == &a)
    unconditionally_reachable_1 = 7;

  // A non-null pointer and a non-matching value (not a null pointer)
  int unreachable_1;
  if(ptr_to_a == &c)
    unreachable_1 = 7;

  // A non-null pointer and a non-matching value (a null pointer)
  int unreachable_2;
  if(ptr_to_a == 0)
    unreachable_2 = 7;

  // A null pointer and a matching value
  int unconditionally_reachable_2;
  if(ptr_to_null == 0)
    unconditionally_reachable_2 = 7;

  // A null pointer and a non-matching value
  int unreachable_3;
  if(ptr_to_null == &a)
    unreachable_3 = 7;

  // Disequality "!="

  // A non-null pointer and a matching value
  int unreachable_4;
  if(ptr_to_a != &a)
    unreachable_4 = 7;

  // A non-null pointer and a non-matching value (not a null pointer)
  int unconditionally_reachable_3;
  if(ptr_to_a != &c)
    unconditionally_reachable_3 = 7;

  // A non-null pointer and a non-matching value (a null pointer)
  int unconditionally_reachable_4;
  if(ptr_to_a != 0)
    unconditionally_reachable_4 = 7;

  // A null pointer and a matching value
  int unreachable_5;
  if(ptr_to_null != 0)
    unreachable_5 = 7;

  // A null pointer and a non-matching value
  int unconditionally_reachable_5;
  if(ptr_to_null != &a)
    unconditionally_reachable_5 = 7;

  // Symex can't tell what ptr_to_a_or_b points to, but we can tell that it
  // doesn't point to some things
  int *ptr_to_a_or_b = nondet_int_array[0] == 0 ? &a : &b;
  int *ptr_to_a_or_b_or_null =
    nondet_int_array[1] == 0 ? &a : nondet_int_array[1] == 1 ? &b : 0;

  // Equality "=="

  // A non-null pointer and a matching value
  int possibly_reachable_1;
  if(ptr_to_a_or_b == &a)
    possibly_reachable_1 = 7;

  // A non-null pointer and a non-matching value (not a null pointer)
  int unreachable_6;
  if(ptr_to_a_or_b == &c)
    unreachable_6 = 7;

  // A non-null pointer and a non-matching value (a null pointer)
  int unreachable_7;
  if(ptr_to_a_or_b == 0)
    unreachable_7 = 7;

  // A possibly-null pointer and a matching value (not a null pointer)
  int possibly_reachable_2;
  if(ptr_to_a_or_b_or_null == &a)
    possibly_reachable_2 = 7;

  // A possibly-null pointer and a matching value (a null pointer)
  int possibly_reachable_3;
  if(ptr_to_a_or_b_or_null == 0)
    possibly_reachable_3 = 7;

  // A possibly-null pointer and a non-matching value
  int unreachable_8;
  if(ptr_to_a_or_b_or_null == &c)
    unreachable_8 = 7;

  // Disequality "!="

  // A non-null pointer and a matching value
  int possibly_reachable_4;
  if(ptr_to_a_or_b != &a)
    possibly_reachable_4 = 7;

  // A non-null pointer and a non-matching value (not a null pointer)
  int unconditionally_reachable_6;
  if(ptr_to_a_or_b != &c)
    unconditionally_reachable_6 = 7;

  // A non-null pointer and a non-matching value (a null pointer)
  int unconditionally_reachable_7;
  if(ptr_to_a_or_b != 0)
    unconditionally_reachable_7 = 7;

  // A possibly-null pointer and a matching value (not a null pointer)
  int possibly_reachable_5;
  if(ptr_to_a_or_b_or_null != &a)
    possibly_reachable_5 = 7;

  // A possibly-null pointer and a matching value (a null pointer)
  int possibly_reachable_6;
  if(ptr_to_a_or_b_or_null != 0)
    possibly_reachable_6 = 7;

  // A possibly-null pointer and a non-matching value
  int unconditionally_reachable_8;
  if(ptr_to_a_or_b_or_null != &c)
    unconditionally_reachable_8 = 7;

  // We should also be able to do all of the above in compound expressions which
  // use logical operators like AND, OR and NOT, or even ternary expressions.

  int unconditionally_reachable_9;
  if(!(ptr_to_a == &c) && ptr_to_a_or_b != 0)
    unconditionally_reachable_9 = 7;

  int unreachable_9;
  if(!(ptr_to_null == 0) || ptr_to_a_or_b == 0)
    unreachable_9 = 7;

  int unconditionally_reachable_10;
  if((ptr_to_a == &a && !(ptr_to_a_or_b == 0)) || ptr_to_a_or_b_or_null == &c)
    unconditionally_reachable_10 = 7;

  int unreachable_10;
  if(ptr_to_a_or_b_or_null != 0 ? ptr_to_null != 0 : ptr_to_a_or_b == &c)
    unreachable_10 = 7;

  // And everything should work with the symbol on the left or the right

  int unconditionally_reachable_11;
  if(!(&c == ptr_to_a) && 0 != ptr_to_a_or_b)
    unconditionally_reachable_11 = 7;

  int unreachable_11;
  if(!(0 == ptr_to_null) || 0 == ptr_to_a_or_b)
    unreachable_11 = 7;

  int unconditionally_reachable_12;
  if((&a == ptr_to_a && !(0 == ptr_to_a_or_b)) || &c == ptr_to_a_or_b_or_null)
    unconditionally_reachable_12 = 7;

  int unreachable_12;
  if(0 != ptr_to_a_or_b_or_null ? 0 != ptr_to_null : &c == ptr_to_a_or_b)
    unreachable_12 = 7;

  int possibly_reachable_7;
  if(0 != ptr_to_a_or_b_or_null)
    possibly_reachable_7 = 7;

  assert(0);
}

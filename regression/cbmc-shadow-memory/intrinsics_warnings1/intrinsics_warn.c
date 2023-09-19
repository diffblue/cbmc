//
// Created by Fotis Koutoulakis on 19/09/2023.
//
#include <assert.h>
#include <stdio.h>

struct S
{
  int i;
  int j;
};

int main()
{
  __CPROVER_field_decl_local("uninitialized", (char)0);
  __CPROVER_field_decl_global("uninitialized-global", (char)0);

  struct S s;
  char a;

  __CPROVER_set_field(&a, "uninitialized", 1);

  assert(__CPROVER_get_field(&a, "uninitialized") == 1);

  __CPROVER_set_field(&s, "uninitialized", 1);

  assert(__CPROVER_get_field(&s, "uninitialized") == 1);
  assert(__CPROVER_get_field(&s.i, "uninitialized") == 1);
  assert(__CPROVER_get_field(&s.j, "uninitialized") == 1);

  return 0;
}

//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// This is just a basic example.
/// Pointer references are tested and ensured, that for example f and f_1 are
/// pointing to the same int value location after running memory-analyzer.

#include "plain_old_datatypes.h"
int my_function(char *s)
{
  int a = 10;
  g->a = a;
  g->b = s;
  return 0;
}

int main(int argc, char **argv)
{
  char *test;

  e = 17;

  f = malloc(sizeof(int));
  f = &e;
  f_1 = f;

  h = "test";

  g = malloc(sizeof(struct mapping_things));
  d.a = 4;
  d.c = -32;
  test = "test2";

  d.b = test;

  my_function(test);

  free(g);
  free(f);

  return 0;
}

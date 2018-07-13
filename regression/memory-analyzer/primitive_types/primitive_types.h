//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// Example1 is just demonstrating, that the tool works in general.
/// A small struct and a few primitive pointers are declared in the global
/// namespace. These are assigned with values before calling my_function
/// and then, it is tested that this global state can be reconstructed before
/// calling my_function. As long as this example work basic functionallity is
/// provided.

#include <stdlib.h>

struct mapping_things
{
  int a;
  char *b;
  int c;
};

typedef struct mapping_things other_things;

other_things d;
int e;
int *f;
int *f_1;
struct mapping_things *g;
char *h;
int my_function(char *s);

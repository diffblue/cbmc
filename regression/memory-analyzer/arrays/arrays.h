//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// Example3 test explicitly the array support.
/// It ensures, that arrays are handled right.
/// The different typedefs have been used, to make sure the memory-analyzer
/// is aware of the different appeareances in the gdb responses.

#include <stdbool.h>

struct a_sub_sub_typet
{
  char *text;
};

typedef struct a_sub_sub_typet messaget;

struct a_sub_typet
{
  int id;
  messaget options[2];
};

struct a_typet
{
  int config[10];
  bool initialized;
  unsigned char values[70];
  struct a_sub_typet childs[4];
} * test_struct;

typedef struct a_sub_typet entryt;

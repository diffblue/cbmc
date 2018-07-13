//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// Example2 deals with cycles in datastructures.
///
/// While it is common that some datastructures contain cylces,
/// it is necessary that the memory-analyzer does recognize them.
/// Otherwise it would follow the datastructures pointer establishing
/// the cycle for ever and never terminate execution.
/// The cycle_buffer described below contains a cycle.
/// As long as this regression test works, cycle introduced by using pointers
/// are handle the correct way.

#include <stdlib.h>
typedef struct cycle_buffer_entry
{
  char *data;
  struct cycle_buffer_entry *next;
} cycle_buffer_entry_t;

struct cycle_buffer
{
  cycle_buffer_entry_t *start;
  struct cycle_buffer_entry *end;
};

struct cycle_buffer buffer;

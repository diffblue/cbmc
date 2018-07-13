//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// This example deals with cyclic data structures,
/// see comment in example2.h explaining why this is necessary.
/// add_element is just declared as a helper method for cycle construction.
/// process_buffer isn't supposed to do meaningfull stuff.
/// It is the hook for the gdb breakpoint used in the test.
/// free_buffer just does clean up, if you run this.

#include "cycles.h"
void add_element(char *content)
{
  cycle_buffer_entry_t *new_entry = malloc(sizeof(cycle_buffer_entry_t));
  new_entry->data = content;
  if(buffer.end && buffer.start)
  {
    new_entry->next = buffer.start;
    buffer.end->next = new_entry;
    buffer.end = new_entry;
  }
  else
  {
    new_entry->next = new_entry;
    buffer.end = new_entry;
    buffer.start = new_entry;
  }
}

int process_buffer()
{
  return 0;
}

void free_buffer()
{
  cycle_buffer_entry_t *current;
  cycle_buffer_entry_t *free_next;
  if(buffer.start)
  {
    current = buffer.start->next;
    while(current != buffer.start)
    {
      free_next = current;
      current = current->next;
      free(free_next);
    }
    free(current);
  }
}

int main()
{
  add_element("snow");
  add_element("sun");
  add_element("rain");
  add_element("thunder storm");

  process_buffer();
  free_buffer();
}

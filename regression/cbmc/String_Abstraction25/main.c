#include <assert.h>
#include <string.h>

int main()
{
  // initialised with a string literal: the buffer size is known
  char from_literal[4] = "yyy";
  assert(__CPROVER_buffer_size(from_literal) == 4);
  // initialised with a list: it is not, with or without a null character
  char from_list[4] = {'y', 'y', 'y', 'y'};
  assert(__CPROVER_buffer_size(from_list) == 4);
  char from_terminated_list[4] = {'y', 'y', 'y', 0};
  assert(__CPROVER_buffer_size(from_terminated_list) == 4);
  // and thus memcpy fails its "memcpy buffer overflow" precondition
  char src[4] = "x";
  memcpy(from_list, src, 2);
  return 0;
}

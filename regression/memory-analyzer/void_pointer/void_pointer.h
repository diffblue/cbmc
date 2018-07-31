//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// Example4 test the handling of void pointer.
/// The memory-analyzer tries to cast them to char and read some of the data.

struct a_struct_with_void
{
  int size;
  void *data;
} blob;

void *a_void_pointer;
void *a_second_void_pointer;
void *a_third_void_pointer;

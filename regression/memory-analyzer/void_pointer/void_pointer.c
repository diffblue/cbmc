//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// This file initializes some void pointer in different styles.
/// Later the memory-analyzer tries to reconstruct the content.

#include "void_pointer.h"
int main()
{
  char *char_pointer = "test_string";
  a_second_void_pointer = char_pointer;
  char bytes[] = {0xf3, 0xf3, 0x48, 0xff, 0x5c, 0x5c, 0xff};
  a_third_void_pointer = &bytes;

  blob.data = bytes;
  blob.size = sizeof(bytes);
  return 0;
}

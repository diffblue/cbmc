//Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

/// \file
/// This file test array support in the memory-analyzer.
/// A more detailed description of the test idea is in example3.h.
/// setup() prepares the data structure.
/// manipulate_data() is the hook used for the test,
/// where gdb reaches the breakpoint.
/// main() is just the required boilerplate around this methods,
/// to make the compiled result executable.

#include "arrays.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void setup()
{
  test_struct = malloc(sizeof(struct a_typet));
  for(int i = 0; i < 10; i++)
  {
    test_struct->config[i] = i + 10;
  }
  for(int i = 0; i < 10; i++)
  {
    test_struct->values[i] = 0xf3;
  }
  for(int i = 10; i < 20; i++)
  {
    test_struct->values[i] = 0x3f;
  }
  for(int i = 20; i < 30; i++)
  {
    test_struct->values[i] = 0x01;
  }
  for(int i = 30; i < 40; i++)
  {
    test_struct->values[i] = 0x01;
  }
  for(int i = 40; i < 50; i++)
  {
    test_struct->values[i] = 0xff;
  }
  for(int i = 50; i < 60; i++)
  {
    test_struct->values[i] = 0x00;
  }
  for(int i = 60; i < 70; i++)
  {
    test_struct->values[i] = 0xab;
  }
  messaget option1 = {.text = "accept"};
  for(int i = 0; i < 4; i++)
  {
    char *value = malloc(sizeof(char *));
    sprintf(value, "unique%i", i);
    entryt your_options = {
      .id = 1, .options[0] = option1, .options[1].text = value};
    your_options.id = i + 12;
    test_struct->childs[i].id = your_options.id;
    test_struct->childs[i].options[0] = your_options.options[0];
    test_struct->childs[i].options[1].text = your_options.options[1].text;
  }
  test_struct->initialized = true;
}

int manipulate_data()
{
  for(int i = 0; i < 4; i++)
  {
    free(test_struct->childs[i].options[1].text);
    test_struct->childs[i].options[1].text = "decline";
  }
}

int main()
{
  setup();
  manipulate_data();
  return 0;
}

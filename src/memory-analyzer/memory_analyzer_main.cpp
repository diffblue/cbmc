// Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>


#include "memory_analyzer_parse_options.h"

int main(int argc, const char **argv)
{
  memory_analyzer_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}

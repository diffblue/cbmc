// Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>
#ifdef __linux__

#include "memory_analyzer_parse_options.h"

int main(int argc, const char **argv)
{
  memory_analyzer_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}
#else
int main()
{
  throw "only supported on Linux platforms currently\n";
}
#endif

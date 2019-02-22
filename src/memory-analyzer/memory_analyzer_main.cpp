// Copyright 2018 Author: Malte Mues <mail.mues@gmail.com>

// clang-format off
#if defined(__linux__) || \
    defined(__FreeBSD_kernel__) || \
    defined(__GNU__) || \
    defined(__unix__) || \
    defined(__CYGWIN__) || \
    defined(__MACH__)
// clang-format on

#include "memory_analyzer_parse_options.h"

int main(int argc, const char **argv)
{
  memory_analyzer_parse_optionst parse_options(argc, argv);
  return parse_options.main();
}

#else

int main()
{
  throw "the memory analyzer is only supported on Unices\n";
}

#endif

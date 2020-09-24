/// \file
/// \author Diffblue Ltd.

#include "goto_unwind_parse_options.h"

int main(int argc, char **argv)
{
  goto_unwind_parse_optionst goto_unwind(argc, const_cast<const char **>(argv));
  return goto_unwind.main();
}

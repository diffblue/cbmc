// Author: Fotis Koutoulakis for Diffblue Ltd.

#ifdef _MSC_VER
#  include <util/unicode.h>
#endif

#include "goto_inspect_parse_options.h"

#ifdef _MSC_VER
int wmain(int argc, const wchar_t **argv_wide)
{
  auto vec = narrow_argv(argc, argv_wide);
  auto narrow = to_c_str_array(std::begin(vec), std::end(vec));
  auto argv = narrow.data();
#else
int main(int argc, const char **argv)
{
#endif
  return goto_inspect_parse_optionst{argc, argv}.main();
}

// N5008 [istream.formatted.arithmetic]/1-3: `std::cin >> i' extracts an
// integer through the num_get facet of the stream's locale
// ([facet.num.get.virtuals]); on failure it stores 0 and sets failbit.
// The characters read from the standard input are unknown, so either
// outcome is possible, and the stream state is good or failed, never bad
// with this input.
#include <iostream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  int i = -1;
  std::cin >> i;
  __CPROVER_assert(!std::cin.bad(), "no read error");
  __CPROVER_assert(!std::cin.fail() || i == 0, "0 stored on failure");
  __CPROVER_assert(std::cin.fail(), "WRONG (must FAIL)");
  return 0;
}

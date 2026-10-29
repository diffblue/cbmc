// N5008 [istream.formatted.arithmetic]/1-3: `std::cin >> i' extracts an
// integer through the num_get facet of the stream's locale
// ([facet.num.get.virtuals]); if the conversion fails it stores 0 and sets
// failbit, and if the value is out of range it stores INT_MAX or INT_MIN
// and sets failbit ([facet.num.get.virtuals]/3, stage 3).
// [istream.formatted.reqmts]/1: if the sentry fails (end of
// file before a character), nothing is extracted and i keeps its value.
// The characters read from the standard input are unknown, so each outcome
// is possible; the stream is never bad with this input.
#include <climits>
#include <iostream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  int i = -1;
  std::cin >> i;
  __CPROVER_assert(!std::cin.bad(), "no read error");
  __CPROVER_assert(
    !std::cin.fail() || i == 0 || i == -1 || i == INT_MAX || i == INT_MIN,
    "failed: 0, a limit, or nothing extracted");
  __CPROVER_assert(std::cin.fail(), "WRONG (must FAIL)");
  return 0;
}

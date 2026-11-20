// N5008 [ostream.inserters.arithmetic]/1, [facet.num.put.virtuals]/1-5:
// an integer is formatted as printf would with the conversion that the
// stream's flags select (Tables 106 and 107), then padded to the field
// width as adjustfield says.
#include <iomanip>
#include <sstream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::ostringstream d, x, X, i, l;
  d << -42;
  __CPROVER_assert(d.str() == "-42", "decimal");
  x << std::hex << 255;
  __CPROVER_assert(x.str() == "ff", "hex");
  X << std::showbase << std::uppercase << std::hex << 255;
  __CPROVER_assert(X.str() == "0XFF", "showbase uppercase");
  i << std::showpos << std::setw(5) << std::internal << 42;
  __CPROVER_assert(i.str() == "+  42", "internal padding");
  l << std::left << std::setw(4) << 7 << '|';
  __CPROVER_assert(l.str() == "7   |", "left padding");
  __CPROVER_assert(l.str() == "7|", "WRONG (must FAIL)");
  return 0;
}

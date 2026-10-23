// N5008 [facet.ctype.char.virtuals]/1, [locale.ctype.virtuals]/11 and /13:
// ctype<char>'s do_widen and do_narrow apply the simplest reasonable
// transformation, for char to char the identity.  libc++ defines these
// virtuals in its shared library.
#include <locale>

extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::locale loc;
  const std::ctype<char> &ct = std::use_facet<std::ctype<char>>(loc);
  __CPROVER_assert(ct.widen('7') == '7', "widen");
  __CPROVER_assert(ct.narrow('x', '?') == 'x', "narrow");
  const char in[3] = {'a', '-', '9'};
  char out[3] = {0, 0, 0};
  const char *end = ct.widen(in, in + 3, out);
  __CPROVER_assert(end == in + 3, "widen of a range returns its end");
  __CPROVER_assert(
    out[0] == 'a' && out[1] == '-' && out[2] == '9', "widened range");
  char back[3] = {0, 0, 0};
  ct.narrow(out, out + 3, '?', back);
  __CPROVER_assert(
    back[0] == 'a' && back[1] == '-' && back[2] == '9', "narrowed range");
  __CPROVER_assert(ct.widen('7') == '8', "WRONG (must FAIL)");
  return 0;
}

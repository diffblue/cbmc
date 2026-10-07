// N5008 [class.bit]/4: a bit-field may have enumeration type.  Printing a
// constant of such a bit-field type (--show-goto-functions) dereferenced an
// empty std::optional and printed a number of about 250000 digits; the
// zero-initialized `_Spec<char> __spec{}` of libstdc++'s <format> took
// most of the 50 minutes --show-goto-functions spent on <format>.
extern "C" void __CPROVER_assert(bool, const char *);

enum align : unsigned char
{
  align_default,
  align_left
};

struct spec
{
  align al : 2;
  unsigned alt : 1;
};

int main()
{
  spec s{};
  __CPROVER_assert(s.al == align_default && s.alt == 0, "zero-initialized");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

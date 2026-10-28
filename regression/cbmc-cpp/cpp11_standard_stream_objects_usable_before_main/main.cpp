// N5008 [iostream.objects.overview]/3, /5: the standard stream objects are
// constructed no later than an ios_base::Init object defined where
// <iostream> is included, so a constructor of an object of static storage
// duration defined after the include can use them.
// [narrow.stream.objects]/2, [wide.stream.objects]/2, /5: cin is tied to
// cout; wcin and wcerr are tied to wcout and wcerr has unitbuf set.
#include <iostream>
extern "C" void __CPROVER_assert(bool, const char *);

struct logger
{
  bool ok;
  logger()
  {
    std::cout << "starting\n";
    ok = std::cout.good();
  }
};
logger early;

int main()
{
  __CPROVER_assert(early.ok, "output before main succeeds");
  __CPROVER_assert(std::cin.tie() == &std::cout, "cin tied to cout");
  __CPROVER_assert(std::clog.tie() == nullptr, "clog not tied");
  __CPROVER_assert(std::wcin.tie() == &std::wcout, "wcin tied to wcout");
  __CPROVER_assert(std::wcerr.tie() == &std::wcout, "wcerr tied to wcout");
  __CPROVER_assert(
    (std::wcerr.flags() & std::ios_base::unitbuf) != 0, "wcerr unitbuf");
  std::cerr << "message";
  __CPROVER_assert(std::cerr.good(), "cerr good after output");
  int c = std::cin.get();
  __CPROVER_assert(c == EOF || (c >= 0 && c <= 255), "cin.get in range");
  __CPROVER_assert(c != EOF, "WRONG (must FAIL)");
  return 0;
}

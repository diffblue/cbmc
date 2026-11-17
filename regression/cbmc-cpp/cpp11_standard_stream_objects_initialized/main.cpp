// N5008 [iostream.objects.overview]/3: the standard stream objects are
// constructed before the body of main.  [narrow.stream.objects]/5: after
// cerr is initialized, cerr.flags() & unitbuf is nonzero and cerr.tie()
// returns &cout; its state is otherwise that of basic_ios<char>::init
// ([basic.ios.cons]/4, Table 140): rdstate() is goodbit, precision() 6.
// cerr and cout are defined in the compiled standard library, not in its
// headers.
#include <iostream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  __CPROVER_assert(std::cerr.good(), "cerr good");
  __CPROVER_assert(std::cerr.precision() == 6, "cerr precision");
  __CPROVER_assert(
    (std::cerr.flags() & std::ios_base::unitbuf) != 0, "cerr unitbuf");
  __CPROVER_assert(std::cerr.tie() == &std::cout, "cerr tied to cout");
  __CPROVER_assert(std::cout.precision() == 6, "cout precision");
  __CPROVER_assert(std::cerr.precision() == 7, "WRONG (must FAIL)");
  return 0;
}

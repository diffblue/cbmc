// N5008 [iostream.objects.overview]/2: the stream buffer of std::cout
// behaves as a basic_filebuf<char> writing to stdout, and a write to stdout
// can fail (stdout closed, a full device); [ostream.unformatted]/7: flush()
// sets badbit when pubsync() returns -1.  `./a.out >/dev/full' makes the
// first assertion fail with g++ and clang++.
#include <iostream>
extern "C" void __CPROVER_assert(bool, const char *);

int main()
{
  std::cout << "x";
  std::cout.flush();
  bool ok = std::cout.good();
  __CPROVER_assert(ok, "a write to stdout always succeeds");
  __CPROVER_assert(!ok, "WRONG (must FAIL)");
  return 0;
}

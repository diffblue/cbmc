// N5008 [dcl.attr.nouniqueaddr]/2 (note): the padding that would
// normally be inserted at the end of a [[no_unique_address]] member may be
// reused by other members.  GCC and Clang (Itanium C++ ABI 2.4 II.2) do so
// for a member of a class that is not POD for the purpose of layout: the
// data size (dsize) of O is 5, and P's c follows at offset 5.
#include <cstddef>
extern "C" void __CPROVER_assert(bool, const char *);
struct O
{
  int i;
  char c;
  O() : i(0), c(0)
  {
  }
};
struct OP
{
  int i;
  char c;
};
struct P
{
  [[no_unique_address]] O o;
  char c;
};
struct PP
{
  [[no_unique_address]] OP o;
  char c;
};
// libc++'s __datasizeof_v<_Tp> (Xcode 26, libc++ 19 and later) measures
// the data size this way and sizes the padding of __compressed_pair by it
template <class T>
struct first_padding_byte
{
  [[no_unique_address]] T v;
  char first_padding_byte_;
};
int main()
{
  P p;
  p.c = 'x';
  p.o.c = 'y';
  __CPROVER_assert(sizeof(P) == 8 && offsetof(P, c) == 5, "tail reused");
  __CPROVER_assert(p.c == 'x' && p.o.c == 'y', "distinct bytes");
  __CPROVER_assert(
    offsetof(first_padding_byte<O>, first_padding_byte_) == 5, "dsize(O)");
  // a POD member's tail padding is not reused (Itanium C++ ABI 2.2)
  __CPROVER_assert(sizeof(PP) == 12 && offsetof(PP, c) == 8, "POD member");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

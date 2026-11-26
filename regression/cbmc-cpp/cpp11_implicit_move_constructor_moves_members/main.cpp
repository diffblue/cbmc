// N5008 [class.copy.ctor]/8: a class without a user-declared copy
// constructor, copy assignment operator, move assignment operator or
// destructor has an implicitly-declared move constructor; /14: it moves
// each member.
#include <utility>
extern "C" void __CPROVER_assert(bool, const char *);

int moves = 0;
int copies = 0;
struct M
{
  M()
  {
  }
  M(const M &)
  {
    ++copies;
  }
  M(M &&) noexcept
  {
    ++moves;
  }
};
struct Holder
{
  M m;
};

int main()
{
  Holder a;
  Holder b(std::move(a));
  __CPROVER_assert(moves == 1 && copies == 0, "member moved");
  __CPROVER_assert(
    noexcept(Holder(std::declval<Holder &&>())), "move is non-throwing");
  __CPROVER_assert(copies == 1, "WRONG (must FAIL)");
  return 0;
}

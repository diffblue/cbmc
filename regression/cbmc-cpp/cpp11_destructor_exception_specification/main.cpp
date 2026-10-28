// N5008 [except.spec]/7: a destructor without a noexcept-specifier is
// potentially-throwing if and only if the destructor of a potentially
// constructed subobject (member, base; [special]/7) is.  An exception
// leaving a non-throwing destructor calls std::terminate
// ([except.terminate]/1.3); one leaving a potentially-throwing destructor
// propagates.  [except.spec]/5.2, [expr.unary.noexcept]/3: the noexcept
// operator sees the destructor calls of an expression, including that of a
// temporary.
#include <exception>
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" int nondet_int();

int which;

void handler()
{
  __CPROVER_assert(which == 1 || which == 4, "terminate: non-throwing");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}

struct Throws
{
  ~Throws() noexcept(false)
  {
    if(which == 2)
      throw 2;
  }
};
struct Plain
{
  ~Plain()
  {
    if(which == 1)
      throw 1;
  }
};
struct HasMember
{
  Throws t;
  ~HasMember()
  {
    if(which == 3)
      throw 3;
  }
};
struct HasBase : Throws
{
};
template <class T>
struct Tpl
{
  ~Tpl()
  {
    if(which == 4)
      throw 4;
  }
};
struct Explicit
{
  ~Explicit() noexcept(false)
  {
    if(which == 5)
      throw 5;
  }
};

int main()
{
  __CPROVER_assert(noexcept(Plain().~Plain()), "plain: non-throwing");
  __CPROVER_assert(!noexcept(HasMember().~HasMember()), "member throws");
  __CPROVER_assert(!noexcept(HasBase().~HasBase()), "base throws");
  __CPROVER_assert(noexcept(Tpl<int>().~Tpl()), "template: non-throwing");
  __CPROVER_assert(!noexcept(Explicit().~Explicit()), "noexcept(false)");
  std::set_terminate(handler);
#ifdef WHICH
  which = WHICH;
#else
  which = nondet_int();
#endif
  try
  {
    if(which == 1)
    {
      Plain p;
    }
    if(which == 2)
    {
      Throws t;
    }
    if(which == 3)
    {
      HasMember h;
    }
    if(which == 4)
    {
      Tpl<int> t;
    }
    if(which == 5)
    {
      Explicit e;
    }
  }
  catch(int)
  {
  }
  return 0;
}

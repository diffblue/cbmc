// N5008 [except.spec]/2: noexcept(constant-expression) has the value of
// the expression as the exception specification, also when it depends on
// template parameters or calls a constexpr function.
// [expr.unary.noexcept]/3, [except.spec]/5.2: the noexcept operator also
// sees the constructor that initializes a temporary.
extern "C" void __CPROVER_assert(bool, const char *);

void may_throw();
void wont_throw() noexcept;

struct Throwing
{
  Throwing()
  {
  }
};
struct NoThrow
{
  NoThrow() noexcept
  {
  }
};

template <class T>
void f() noexcept(noexcept(T()))
{
}
constexpr bool yes()
{
  return true;
}
void g() noexcept(yes())
{
}
void h() noexcept(noexcept(may_throw()))
{
}
void k() noexcept(noexcept(wont_throw()))
{
}

int main()
{
  __CPROVER_assert(!noexcept(Throwing()), "constructor of a temporary");
  __CPROVER_assert(noexcept(NoThrow()), "non-throwing constructor");
  __CPROVER_assert(noexcept(f<int>()), "noexcept(noexcept(int()))");
  __CPROVER_assert(!noexcept(f<Throwing>()), "dependent: Throwing");
  __CPROVER_assert(noexcept(f<NoThrow>()), "dependent: NoThrow");
  __CPROVER_assert(noexcept(g()), "constexpr function");
  __CPROVER_assert(!noexcept(h()), "noexcept(noexcept(may_throw()))");
  __CPROVER_assert(noexcept(k()), "noexcept(noexcept(wont_throw()))");
  __CPROVER_assert(noexcept(h()), "WRONG (must FAIL)");
  return 0;
}

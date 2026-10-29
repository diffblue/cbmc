// N5008 [class.mem.general]/9.4: the noexcept-specifier of a member
// function is a complete-class context; [expr.prim.this]/4: `b()' in it
// calls this->b().  [except.spec]/12: in a class template specialization
// it is instantiated when needed.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
struct W
{
  void a() noexcept(noexcept(b()))
  {
  }
  void b() noexcept(sizeof(T) == 1)
  {
  }
};

int main()
{
  W<char> wc;
  W<int> wi;
  __CPROVER_assert(noexcept(wc.a()), "names a later non-throwing member");
  __CPROVER_assert(!noexcept(wi.a()), "names a later throwing member");
  __CPROVER_assert(noexcept(wi.a()), "WRONG (must FAIL)");
  return 0;
}

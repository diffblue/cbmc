// N5008 [class.mem.general]/9.4: the noexcept-specifier of a member
// function is a complete-class context, so it can name members declared
// later in the class; [except.spec]/2.
extern "C" void __CPROVER_assert(bool, const char *);

struct S
{
  void a() noexcept(noexcept(b()))
  {
  }
  void b()
  {
  }
  void c() noexcept(noexcept(d()))
  {
  }
  void d() noexcept
  {
  }
};

int main()
{
  S s;
  __CPROVER_assert(!noexcept(s.a()), "names a later throwing member");
  __CPROVER_assert(noexcept(s.c()), "names a later non-throwing member");
  __CPROVER_assert(noexcept(s.a()), "WRONG (must FAIL)");
  return 0;
}

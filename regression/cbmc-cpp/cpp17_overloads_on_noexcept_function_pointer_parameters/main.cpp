// N5008 [conv.fctptr]/1: a pointer to noexcept function converts to a
// pointer to function, not the other way round; the conversion is in the
// Exact Match category but worse than the identity ([over.ics.rank]/3.2.1),
// so overloads on `void (*)() noexcept' and `void (*)()' are distinct and
// selected by the argument's exception specification.
extern "C" void __CPROVER_assert(bool, const char *);
void t()
{
}
void q() noexcept
{
}
struct S
{
  static void st()
  {
  }
  static void sq() noexcept
  {
  }
  void mt()
  {
  }
  void mq() noexcept
  {
  }
};
bool k(void (*)() noexcept)
{
  return true;
}
bool k(void (*)())
{
  return false;
}
bool m(void (S::*)() noexcept)
{
  return true;
}
bool m(void (S::*)())
{
  return false;
}
int main()
{
  __CPROVER_assert(!k(&t) && k(&q), "free functions");
  __CPROVER_assert(!k(&S::st) && k(&S::sq), "static member functions");
  __CPROVER_assert(!m(&S::mt) && m(&S::mq), "pointers to member functions");
  void (*p)() = q;
  __CPROVER_assert(p == &q, "noexcept to plain pointer");
  __CPROVER_assert(k(&t), "WRONG (must FAIL)");
}

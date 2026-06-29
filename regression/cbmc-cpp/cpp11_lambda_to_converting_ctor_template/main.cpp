// N5008 [over.match.best]/[over.ics.user], [class.conv.ctor]: forming the
// implicit conversion sequence from a closure (lambda) argument to a class
// parameter whose only converting constructor is a *template* -- the shape of
// passing a lambda to a `std::function<...>` parameter -- must consider that
// converting-constructor template.
//
// Regression: CBMC dropped this user-defined conversion.  A closure argument is
// a prvalue of struct (closure) type; constructing the target temporary
// re-type-checked that struct-typed argument and aborted internally with
// "unexpected expression: struct", so overload resolution reported "found no
// match".  (A named class argument in the same position worked, masking it.)
//
// Header-free and non-vacuous: assertion 2 is a deliberately wrong claim that
// must FAIL.

extern "C" void __CPROVER_assert(int, const char *);
extern int nondet_int(void);

struct Callable
{
  int tag;
  template <class F>
  Callable(F) : tag(42)
  {
  }
};

int use(int w, Callable c)
{
  (void)w;
  return c.tag;
}

int main()
{
  int r = use(nondet_int(), [](int i) { return i > 0; }); // lambda -> Callable
  __CPROVER_assert(r == 42, "lambda converted via constructor template");
  __CPROVER_assert(r == 0, "WRONG must FAIL");
  return 0;
}

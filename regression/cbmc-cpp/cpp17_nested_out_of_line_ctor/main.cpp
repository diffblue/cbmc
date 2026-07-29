// Header-free: the OUT-OF-LINE definition of a NESTED class's
// constructor inside a class template (Outer<T>::sentry::sentry) is
// never attached to the instantiated member ("no body for callee
// sentry::sentry").  The shape of libc++ basic_ostream's sentry.
// Found while validating the typename-constructor parse rule (the
// rule correctly leaves this name a constructor; the body loss is a
// separate, pre-existing defect).  g++/clang++/valgrind run clean.

extern "C" void __CPROVER_assert(bool, const char *);
template <class T> struct Outer {
  struct sentry {
    sentry(Outer &o);
    bool ok_;
  };
  int v;
};
template <class T> Outer<T>::sentry::sentry(Outer<T> &o) : ok_(false) {
  if (o.v)
    ok_ = true;
}
int main() {
  Outer<int> o;
  o.v = 1;
  Outer<int>::sentry s(o);
  __CPROVER_assert(s.ok_, "nested out-of-line ctor ran");
  return 0;
}

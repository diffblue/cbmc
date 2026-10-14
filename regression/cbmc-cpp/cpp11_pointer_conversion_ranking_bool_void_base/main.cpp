// N5008 [over.ics.rank]/4.1: a conversion that does not convert a pointer
// to bool is better than one that does; /4.4.2: converting a pointer to a
// class to a pointer to its base is better than to `void *'.  With
// overloads for bool, const void * and sbuf *, a stringbuf * argument
// (stringbuf derived from sbuf) selects the sbuf * overload, and an int *
// the const void * one.  All three conversions had the same rank and the
// call was ambiguous -- `out << in.rdbuf()' with std::ostream's inserters
// for bool, const void * and basic_streambuf * (CBMC's own goto-cc
// compile.cpp and ld_mode.cpp, dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct sbuf
{
  int n = 3;
};
struct stringbuf : sbuf
{
};
int f(bool)
{
  return 1;
}
int f(const void *)
{
  return 2;
}
int f(sbuf *)
{
  return 3;
}
struct ostr
{
  int got = 0;
  ostr &operator<<(bool)
  {
    got = 1;
    return *this;
  }
  ostr &operator<<(const void *)
  {
    got = 2;
    return *this;
  }
  ostr &operator<<(sbuf *b)
  {
    got = 100 + b->n;
    return *this;
  }
};
int main()
{
  stringbuf b;
  int i = 0;
  __CPROVER_assert(f(&b) == 3, "derived-to-base pointer beats void * and bool");
  __CPROVER_assert(f(&i) == 2, "void * beats bool");
  ostr out;
  out << &b;
  __CPROVER_assert(out.got == 103, "member inserter");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

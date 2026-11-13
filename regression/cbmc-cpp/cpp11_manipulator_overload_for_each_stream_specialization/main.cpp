// N5008 [over.match.oper]/3, [over.over]/1, [temp.deduct.funcaddr]/1: in
// `o << endl', with endl a function template, the candidate taking a
// pointer to function deduces endl's template arguments from its parameter
// type; the candidate taking bool is not viable, as an overload set has no
// conversion to bool.  This is how std::endl is inserted into a stream.
extern "C" void __CPROVER_assert(bool, const char *);

template <class C>
struct os
{
  int which = 0;
  os &operator<<(bool)
  {
    which = 1;
    return *this;
  }
  os &operator<<(os &(*f)(os &))
  {
    return f(*this);
  }
};

template <class C>
os<C> &endl(os<C> &o)
{
  o.which = 2;
  return o;
}

int main()
{
  os<char> o;
  os<wchar_t> w;
  o << endl;
  w << endl;
  __CPROVER_assert(o.which == 2, "manipulator for os<char>");
  __CPROVER_assert(w.which == 2, "manipulator for os<wchar_t>");
  __CPROVER_assert(w.which == 1, "WRONG (must FAIL)");
  return 0;
}

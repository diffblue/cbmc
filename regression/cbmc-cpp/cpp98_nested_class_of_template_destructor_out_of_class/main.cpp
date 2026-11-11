// N5008 [temp.mem.class]/1, [class.nest]/3: a member of a nested class of
// a class template may be defined out of class, `outer<T>::inner::~inner'
// for the destructor too (libc++'s basic_ostream<C, T>::sentry::~sentry,
// which flushes the stream, [ostream.sentry]/4).  The destructor's
// definition was dropped: it had no body, and inner's destructor never ran.
extern "C" void __CPROVER_assert(bool, const char *);
int log_ctor = 0, log_dtor = 0, log_fn = 0;
template <class T>
struct outer
{
  struct inner
  {
    inner(int);
    ~inner();
    int f();
    int v;
  };
};
template <class T>
outer<T>::inner::inner(int x) : v(x)
{
  ++log_ctor;
}
template <class T>
outer<T>::inner::~inner()
{
  ++log_dtor;
}
template <class T>
int outer<T>::inner::f()
{
  ++log_fn;
  return v;
}
int main()
{
  {
    outer<int>::inner i(3);
    __CPROVER_assert(i.f() == 3, "member function");
  }
  __CPROVER_assert(log_ctor == 1, "constructor ran");
  __CPROVER_assert(log_fn == 1, "member function ran");
  __CPROVER_assert(log_dtor == 1, "destructor ran");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

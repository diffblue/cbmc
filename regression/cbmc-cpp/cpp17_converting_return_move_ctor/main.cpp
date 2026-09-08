// N5008 [stmt.return]/2 + [dcl.init.general]/16.6.1: the result object
// is COPY-INITIALIZED from the return operand, which considers the
// class's constructors -- including a CONVERTING one
// (`template <class U> uptr(uptr<U> &&)`, the
// [unique.ptr.single.ctor]/26 shape).  CBMC materialised the result
// object through a constructor only when the return type had a
// DESTRUCTOR, and skipped operands that were already temporaries, so a
// converting temporary of a different class type fell through to
// implicit_typecast (which knows no user-defined conversion) and failed
// with "invalid implicit conversion from 'struct uptr' to 'struct
// uptr'".  Found dog-fooding src/util/timestamper.cpp's factory; the
// same conversion in DIRECT-INITIALIZATION always worked.
extern "C" void __CPROVER_assert(bool, const char *);
struct base_t
{
  virtual int id() const
  {
    return 1;
  }
};
struct derived_t : base_t
{
  int id() const override
  {
    return 2;
  }
};
template <class T> struct uptr
{
  T *p_;
  explicit uptr(T *p) : p_(p)
  {
  }
  // converting move constructor ([unique.ptr.single.ctor]/26 shape)
  template <class U> uptr(uptr<U> &&o) : p_(o.release())
  {
  }
  T *release()
  {
    T *r = p_;
    p_ = nullptr;
    return r;
  }
  T *operator->() const
  {
    return p_;
  }
};
enum kindt
{
  PLAIN,
  DERIVED
};
uptr<const base_t> make(kindt)
{
  return uptr<const derived_t>(new derived_t());
}
int main()
{
  __CPROVER_assert(make(DERIVED)->id() == 2, "converting return in switch");
  return 0;
}

extern "C" void __CPROVER_assert(bool, const char *);
template <int N>
struct base
{
  template <int I>
  bool is_derived() const
  {
    return tag == I;
  }
  int tag;
};
struct holder
{
  base<2> *p;
  base<2> r;
  bool direct() const
  {
    return p->is_derived<1>();
  }
  template <int I>
  bool via_obj() const
  {
    return r.template is_derived<I>();
  }
  template <int I>
  bool via_deref() const
  {
    return (*p).template is_derived<I>();
  }
  template <int I>
  bool via_ptr() const
  {
    return p->template is_derived<I>();
  }
};
int main()
{
  base<2> b;
  b.tag = 1;
  holder h;
  h.p = &b;
  h.r = b;
  __CPROVER_assert(
    h.direct(), "non-template context, explicit arg through pointer");
  __CPROVER_assert(h.via_obj<1>(), "object.template f<I>()");
  __CPROVER_assert(h.via_deref<1>(), "(*p).template f<I>()");
  __CPROVER_assert(h.via_ptr<1>(), "p->template f<I>()");
  return 0;
}

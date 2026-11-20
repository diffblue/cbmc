extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [temp.over.link]/3, [defns.signature.member.templ]: the return type
// is part of a member function template's signature, so the two put
// templates, which differ only there, are different templates, each
// defined out of line (libc++'s __split_buffer::__construct_at_end)
template <bool, class T = void>
struct enable_if
{
};
template <class T>
struct enable_if<true, T>
{
  using type = T;
};
template <bool B, class T = void>
using enable_if_t = typename enable_if<B, T>::type;
template <class T>
struct is_fwd
{
  static constexpr bool value = sizeof(T) == sizeof(void *);
};
template <class T>
struct buf
{
  int n = 0;
  template <class I>
  enable_if_t<!is_fwd<I>::value> put(I, I);
  template <class I>
  enable_if_t<is_fwd<I>::value> put(I, I);
};
template <class T>
template <class I>
enable_if_t<!is_fwd<I>::value> buf<T>::put(I, I)
{
  n = 1;
}
template <class T>
template <class I>
enable_if_t<is_fwd<I>::value> buf<T>::put(I, I)
{
  n = 2;
}
// the same in a class that is not a template
struct plain
{
  int n = 0;
  template <class I>
  enable_if_t<!is_fwd<I>::value> put(I, I);
  template <class I>
  enable_if_t<is_fwd<I>::value> put(I, I);
};
template <class I>
enable_if_t<!is_fwd<I>::value> plain::put(I, I)
{
  n = 1;
}
template <class I>
enable_if_t<is_fwd<I>::value> plain::put(I, I)
{
  n = 2;
}
int main()
{
  plain q;
  int *p0 = nullptr;
  q.put(p0, p0);
  __CPROVER_assert(q.n == 2, "non-template class");
  buf<int> b;
  int *p = nullptr;
  b.put(p, p);
  __CPROVER_assert(b.n == 2, "pointer");
  b.put('a', 'b');
  __CPROVER_assert(b.n == 1, "char");
  __CPROVER_assert(b.n == 2, "WRONG (must FAIL)");
}

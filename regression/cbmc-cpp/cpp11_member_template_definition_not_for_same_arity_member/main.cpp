extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct str
{
  typedef unsigned long size_type;
  static const size_type npos = -1;
  C c[2];
  template <class T>
  size_type find(const T &, size_type pos) const;
  size_type find(C ch, size_type pos = 0) const;
};
// N5008 [temp.explicit]/12: an explicit instantiation declaration names
// str<char>, whose members are defined below.  N5008 [temp.mem]/1: the
// member template's definition defines its specializations only, not the
// non-template find of the same name and arity.
extern template const str<char>::size_type str<char>::npos;
template <class C>
template <class T>
typename str<C>::size_type str<C>::find(const T &, size_type) const
{
  return 77;
}
template <class C>
typename str<C>::size_type str<C>::find(C ch, size_type pos) const
{
  for(size_type i = pos; i < 2; ++i)
    if(c[i] == ch)
      return i;
  return npos;
}
template <class C>
const typename str<C>::size_type str<C>::npos;
int main()
{
  str<char> s{{'a', 'b'}};
  __CPROVER_assert(s.find('b') == 1, "non-template member");
  __CPROVER_assert(s.find(1.0, 0) == 77, "member template");
  __CPROVER_assert(s.find('b') == 77, "WRONG (must FAIL)");
  return 0;
}

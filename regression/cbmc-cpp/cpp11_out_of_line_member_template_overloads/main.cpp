// N5008 [dcl.fct]/3,5 + [temp.over.link]: the out-of-line definition that
// belongs to a member (template) is the one with the same signature; the
// definition may name its parameters -- function and template parameters --
// differently.  Same-named member templates of equal arity were matched by
// name alone, so libstdc++ 16 basic_string's forward-iterator
// `_M_construct(_FwdIt, _FwdIt, forward_iterator_tag)' received the
// input-iterator definition's body, and a member whose definition renamed a
// parameter (`__c' vs `__str') kept the declaration's name and its body was
// dropped ("symbol '__str' is unknown").
extern "C" void __CPROVER_assert(bool, const char *);
struct input_iterator_tag
{
};
struct forward_iterator_tag : input_iterator_tag
{
};
template <class C>
struct str
{
  C buf[16];
  unsigned long len;
  template <class InIt>
  void construct(InIt beg, InIt end, input_iterator_tag);
  template <class FwdIt>
  void construct(FwdIt beg, FwdIt end, forward_iterator_tag);
  void construct(unsigned long req, C c);
  template <bool Terminated>
  void construct(const C *c, unsigned long n);
  str(const C *s)
  {
    construct(s, s + 3, forward_iterator_tag());
  }
  str(const C *s, unsigned long n)
  {
    construct<true>(s, n);
  }
  str(unsigned long n, C c)
  {
    construct(n, c);
  }
};
template <class C>
template <class InIt>
void str<C>::construct(InIt beg, InIt end, input_iterator_tag)
{
  len = 0;
  while(beg != end)
    buf[len++] = *beg++;
}
template <class Ch>
template <class It>
void str<Ch>::construct(It first, It last, forward_iterator_tag)
{
  len = 0;
  for(; first != last; ++first)
    buf[len++] = *first;
  buf[len] = Ch();
}
template <class C>
void str<C>::construct(unsigned long count, C fill)
{
  for(len = 0; len < count; ++len)
    buf[len] = fill;
}
template <class C>
template <bool Terminated>
void str<C>::construct(const C *source, unsigned long n)
{
  for(unsigned long i = 0; i < n; ++i)
    buf[i] = source[i];
  len = n;
  if(Terminated)
    buf[n] = C();
}
int main()
{
  str<char> s("abc");
  __CPROVER_assert(
    s.len == 3 && s.buf[2] == 'c' && s.buf[3] == 0,
    "forward iterator overload");
  str<char> t("xy", 2);
  __CPROVER_assert(t.len == 2 && t.buf[1] == 'y', "bool template overload");
  str<char> u(4, 'z');
  __CPROVER_assert(u.len == 4 && u.buf[3] == 'z', "non-template overload");
  __CPROVER_assert(t.len == 3, "WRONG (must FAIL)");
}

// N5008 [temp.inst]/2-3: out_iter<char>'s member typedef names
// ostream<char> without requiring it to be complete, so ostream<char> need
// not be instantiated while its base ios<...> is being instantiated; once
// complete, ostream<char> has the members of its base (the libstdc++
// basic_ios / ostreambuf_iterator / basic_ostream shape, reduced from
// <sstream> `o << 4')
extern "C" void __CPROVER_assert(bool, const char *);
template <class>
struct traits;
template <class C, class = C>
struct ostream;
template <class C, class T = traits<C>>
struct ostringstream;
template <class C, class T>
struct ostringstream : ostream<char, T>
{
};
struct ios_base
{
  int flags;
  virtual ~ios_base()
  {
  }
};
template <class>
struct out_iter
{
  typedef ostream<char, traits<char>> ostream_type;
};
template <class>
struct num_put
{
  int put(long v) const
  {
    return int(v) + 1;
  }
};
template <class>
struct ios : ios_base
{
  typedef num_put<out_iter<char>> num_put_type;
  num_put_type *np;
};
template <class C, class T>
struct ostream : virtual ios<traits<char>>
{
  int operator<<(int n)
  {
    return insert(n);
  }
  template <class V>
  int insert(V v)
  {
    return this->np->put(v);
  }
};
template <class>
struct istream : ios<traits<char>>
{
  istream &ignore(long);
};
template <>
istream<char> &istream<char>::ignore(long);
int main()
{
  ostringstream<char> o;
  num_put<out_iter<char>> facet;
  o.np = &facet;
  __CPROVER_assert((o << 4) == 5, "member of the virtual base");
  __CPROVER_assert((o << 4) == 4, "WRONG (must FAIL)");
}

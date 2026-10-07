// N5008 [over.match.oper]/3: for `a << b' the member candidates
// (a.operator<<(b)) and the non-member candidates (operator<<(a, b)) form
// one set, ranked by [over.match.best]/2.1.  A member found first must not
// hide a non-member with a better conversion sequence.
extern "C" void __CPROVER_assert(bool, const char *);

struct stream_base
{
  int last;
  stream_base() : last(0)
  {
  }
  stream_base &operator<<(int)
  {
    last = 1;
    return *this;
  }
};

struct stream : stream_base
{
};

// exact match for the char operand; the member needs a promotion
stream &operator<<(stream &s, char)
{
  s.last = 2;
  return s;
}

template <class T>
struct tstream : stream_base
{
};

template <class T>
tstream<T> &operator<<(tstream<T> &s, char)
{
  s.last = 3;
  return s;
}

int main()
{
  stream s;
  s << 'c';
  __CPROVER_assert(s.last == 2, "non-member exact match chosen");
  // the non-member is not viable for a stream_base object
  stream_base b;
  b << 'c';
  __CPROVER_assert(b.last == 1, "member chosen");

  tstream<char> t;
  t << 'c';
  __CPROVER_assert(t.last == 3, "non-member template exact match chosen");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

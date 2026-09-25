// N5008 [class.union.anon]/1, [expr.ref]/6.2: a member of an anonymous union
// is a member of the enclosing class, and an lvalue when the object is.  An
// array member of an anonymous union indexed with a non-constant on the left
// of an assignment was rejected as "not an lvalue" (the intermediate
// anonymous-member subobject lacked the lvalue marking when the expression
// was type-checked a second time) -- libstdc++ 16's
// `_M_local_buf[__len++] = *__beg' in basic_string::_M_construct.
extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
struct str
{
  enum
  {
    cap = 15 / sizeof(C)
  };
  union
  {
    C local_buf[cap + 1];
    unsigned long allocated_capacity;
  };
  unsigned long len = 0;
  void construct(const C *b, const C *e)
  {
    while(b != e && len < cap)
    {
      local_buf[len++] = *b;
      ++b;
    }
    local_buf[len] = C();
  }
  C at(unsigned long i) const
  {
    return local_buf[i];
  }
};
struct plain
{
  union
  {
    char buf[8];
    unsigned long cap;
  };
  int n = 0;
  void put(char c)
  {
    buf[n++] = c;
  }
  void put_at(int i, char c)
  {
    buf[i] = c;
  }
};
int main()
{
  str<char> s;
  const char *lit = "abc";
  s.construct(lit, lit + 3);
  __CPROVER_assert(
    s.len == 3 && s.at(0) == 'a' && s.at(2) == 'c' && s.at(3) == 0,
    "array in anonymous union, template");
  plain p;
  p.put('x');
  p.put_at(1, 'y');
  __CPROVER_assert(
    p.buf[0] == 'x' && p.buf[1] == 'y', "array in anonymous union");
  __CPROVER_assert(s.at(1) == 'x', "WRONG (must FAIL)");
}

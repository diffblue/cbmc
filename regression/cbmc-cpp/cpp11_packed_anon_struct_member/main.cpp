// GNU attribute on a member class definition: the parser's merge_types
// wrapped the struct in a merged_type and the remainder of rClassSpec
// attached the TAG and BODY to the WRAPPER, leaving the struct subtype
// bodyless -- so an attributed anonymous member (libc++ <string>'s
//   struct __attribute__((__packed__)) { size_type __is_long_ : 1;
//                                        size_type __cap_ : ...; };
// rep) stayed an incomplete non-anonymous stub and its members never
// resolved ("symbol '__cap_' is unknown"); a NAMED attributed nested
// struct ("inner" below) was likewise unknown.  Ill-formed per no
// clause -- GNU anonymous structs follow [class.union.anon]/1's
// injection model; the attribute must not change name binding.
extern "C" void __CPROVER_assert(bool, const char *);

template <class _Alloc>
struct basic_string
{
  typedef typename _Alloc::size_type size_type;
  struct __long
  {
    struct __attribute__((__packed__))
    {
      size_type __is_long_ : 1;
      size_type __cap_ : sizeof(size_type) * 8 - 1;
    };
    size_type __size_;
  };
  __long __l;
  basic_string()
  {
    __l.__size_ = 5;
    __l.__cap_ = 7;
    __l.__is_long_ = 1;
  }
  size_type __get_long_cap()
  {
    return __l.__cap_;
  }
};

struct alloc
{
  typedef unsigned long size_type;
};

struct outer
{
  struct __attribute__((__packed__)) inner
  {
    int a;
  };
  inner i;
};

int main()
{
  basic_string<alloc> s;
  __CPROVER_assert(s.__get_long_cap() == 7, "packed anon bitfield");
  outer o;
  o.i.a = 3;
  __CPROVER_assert(o.i.a == 3, "named packed nested");
  return 0;
}

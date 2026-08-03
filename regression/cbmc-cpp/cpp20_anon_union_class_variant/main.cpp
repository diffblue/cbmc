// N5008 [class.union.anon]/1: an anonymous union must not have member
// functions or static data members -- but its variant members MAY be
// of class type with bases and constructors (POD-ness is not
// required).  CBMC's POD gate rejected the enclosing class and every
// use of the variant members failed with "symbol '__null_state_' is
// unknown" (libc++'s __optional_destruct_base, the root of
// std::map's CONVERSION ERROR).  cvise-reduced from a preprocessed
// <map> TU; g++/clang++ accept and run clean.
extern "C" void __CPROVER_assert(bool, const char *);

struct __non_trivial_if
{
};
struct allocator : __non_trivial_if
{
};

template <class>
struct __optional_destruct_base
{
  union {
    char __null_state_;
    allocator __val_;
  };
  __optional_destruct_base() : __null_state_()
  {
  }
};

__optional_destruct_base<int> g;

int main()
{
  g.__null_state_ = 3;
  __CPROVER_assert(g.__null_state_ == 3, "variant member accessible");
}

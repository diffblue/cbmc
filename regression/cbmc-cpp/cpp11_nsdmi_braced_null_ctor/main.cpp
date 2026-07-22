// A default member initializer (NSDMI) `shared_ptrt nothing{0}` where
// the class has constructors from shared_ptrt&& and from
// std::nullptr_t: list-initialization considers both, but only the
// nullptr_t one is viable -- 0 is a null pointer constant
// ([conv.ptr]/1) and binding shared_ptrt&& to 0 would need a
// user-defined conversion, which [over.best.ics.general]/4 excludes
// here.  g++ and clang++ pick the nullptr_t constructor; CBMC reports
// "symbol 'shared_ptrt' does not uniquely resolve".  The SAME
// initializer for a local variable works -- only the NSDMI path
// ([class.mem.general]/10) is affected.  Distilled from
// std::shared_ptr use in analyses/variable-sensitivity/
// abstract_value_object.h (value_range_implementationt); blocks the
// abstract_environment.cpp dog-food TU.
extern "C" void __CPROVER_assert(bool, const char *);

struct shared_ptrt
{
  int tag;
  shared_ptrt(shared_ptrt &&r) : tag(2)
  {
  }
  shared_ptrt(decltype(nullptr)) : tag(1)
  {
  }
};

struct value_ranget
{
  shared_ptrt nothing{0};
};

int main()
{
  value_ranget v;
  __CPROVER_assert(v.nothing.tag == 1, "NSDMI picks the nullptr_t ctor");
  return 0;
}

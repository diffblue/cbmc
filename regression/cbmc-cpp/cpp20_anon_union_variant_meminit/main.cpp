// The next layer above cpp20_anon_union_class_variant: a constructor
// mem-initializer NAMING a variant member of the anonymous union
// ([class.base.init]/2 -- any member of the class, including members
// of anonymous-union members) is silently DROPPED: the constructor
// converts to an empty body and __null_state_ stays nondeterministic.
// g++/clang++ accept and verify at runtime.
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

int main()
{
  __optional_destruct_base<int> b;
  __CPROVER_assert(b.__null_state_ == 0, "variant member value-initialized");
}

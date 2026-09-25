// N5008 [temp.inst]/1-2: a class template specialization is implicitly
// instantiated only when a complete type is required; naming it in an alias
// declaration does not.  [temp.alias]/2: an alias template's template-id is
// equivalent to the type it denotes -- still just a type name.
//
// The libstdc++ 11 <string> shape: `namespace pmr { template <class T>
// class polymorphic_allocator; template <class C, class T = char_traits<C>>
// using basic_string = std::basic_string<C, T, polymorphic_allocator<C>>;
// using string = basic_string<char>; }' with the allocator completed later
// (<memory_resource>).  Instantiating at the alias laid the class out with an
// incomplete member type, and the member was never constructed.

extern "C" void __CPROVER_assert(bool, const char *);

template <class C>
struct traits
{
};

template <class C, class T, class A>
struct basic_str
{
  C c;
  A a; // requires a complete allocator when the class is instantiated
  basic_str() : c(0)
  {
  }
};

namespace pmr
{
template <class T>
class poly_alloc; // only declared here

template <class C, class T = traits<C>>
using basic_str = ::basic_str<C, T, poly_alloc<C>>;

// through the alias template: must not instantiate ::basic_str<...> yet
using str = basic_str<char>;
using wstr = basic_str<wchar_t>;

// directly: likewise
using str2 = ::basic_str<char, traits<char>, poly_alloc<char>>;

template <class T>
class poly_alloc
{
public:
  int k;
  poly_alloc() : k(3)
  {
  }
};
} // namespace pmr

int main()
{
  pmr::str s; // the point of instantiation: poly_alloc<char> is complete
  __CPROVER_assert(s.a.k == 3, "member constructed (alias template)");
  pmr::str2 s2;
  __CPROVER_assert(s2.a.k == 3, "member constructed (alias)");
  __CPROVER_assert(
    sizeof(pmr::str) == 2 * sizeof(int), "layout has the member");
  return 0;
}

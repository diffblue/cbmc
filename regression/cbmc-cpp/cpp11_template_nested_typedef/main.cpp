// Per [temp.res]/4 and [temp.inst]/2: a typedef of the form
//     typedef typename Dep<T>::nested alias;
// inside a class template is a dependent name.  At instantiation time,
// the compiler must instantiate Dep<T> enough to look up the nested
// name and propagate its type.
//
// This reduces the macOS libc++ basic_string pattern:
//     typedef allocator_traits<_Allocator>        __alloc_traits;
//     typedef typename __alloc_traits::pointer    pointer;
//     typedef typename __alloc_traits::size_type  size_type;

template <class A>
struct Traits
{
  typedef A value_type;
  typedef int size_type;
};

template <class T>
struct Wrap
{
  typedef Traits<T> alloc_traits;
  typedef typename alloc_traits::value_type value;
  typedef typename alloc_traits::size_type index;
  value data;
  index count;
};

int main()
{
  Wrap<int> w;
  w.data = 42;
  w.count = 1;
  __CPROVER_assert(w.data == 42, "nested typedef 'value' usable");
  __CPROVER_assert(w.count == 1, "nested typedef 'index' usable");
  return 0;
}

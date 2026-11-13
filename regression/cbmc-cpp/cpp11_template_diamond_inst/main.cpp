// Per [temp.inst]: two templates that reference each other's nested
// names at instantiation time must converge (no infinite recursion)
// because the implicit instantiation of each only needs the
// *declaration* of the other until completeness is required.
//
// This is a guard-rail test for whatever fix we land for the
// eager-instantiation path: we must not introduce divergence when
// templates refer to each other.

template <class T>
struct A;

template <class T>
struct B
{
  typedef T value_type;
  // mention A<T> only as a pointer — no completeness required
  A<T> *buddy;
};

template <class T>
struct A
{
  typedef T value_type;
  B<T> *buddy;
  T data;
};

int main()
{
  A<int> a;
  B<int> b;
  a.data = 5;
  a.buddy = &b;
  b.buddy = &a;
  __CPROVER_assert(a.data == 5, "A<int>::data usable");
  __CPROVER_assert(a.buddy == &b, "A<int>::buddy points to B<int>");
  __CPROVER_assert(b.buddy == &a, "B<int>::buddy points to A<int>");
  return 0;
}

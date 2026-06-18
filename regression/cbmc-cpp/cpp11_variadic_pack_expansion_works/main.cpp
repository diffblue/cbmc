// C++ [temp.variadic] pack-expansion contexts that CBMC already handles
// correctly.  This locks in the working behaviour so the unified
// pack-expansion rework (doc/architectural/cpp-variadic-pack-expansion-rework.md)
// does not regress it.  Header-free.

// Value-pack expansion in a function-call argument list ([temp.variadic]/5),
// single, multiple, and forwarded through two layers.
int g1(int a) { return a; }
int g3(int a, int b, int c) { return a * 100 + b * 10 + c; }
template <typename... A> int call1(A... a) { return g1(a...); }
template <typename... A> int call3(A... a) { return g3(a...); }
template <typename... A> int inner(A... a) { return g3(a...); }
template <typename... A> int outer(A... a) { return inner(a...); }

// Type-pack forwarded as a class-template argument ([temp.arg]).
template <typename... T> struct tup { int count() const { return sizeof...(T); } };
template <typename... T> struct wrap { typedef tup<T...> type; };

// sizeof...(T) in a member function body ([temp.variadic]/8).
template <typename... T> struct holder { int n() const { return sizeof...(T); } };

int main()
{
  int x, y, z;
  __CPROVER_assume(x >= 0 && x < 10 && y >= 0 && y < 10 && z >= 0 && z < 10);
  __CPROVER_assert(call1(x) == x, "value-pack call, 1 element");
  __CPROVER_assert(call3(x, y, z) == g3(x, y, z), "value-pack call, 3 elements");
  __CPROVER_assert(outer(x, y, z) == g3(x, y, z), "value-pack forward, two layers");

  wrap<int, char, long>::type t;
  __CPROVER_assert(t.count() == 3, "type-pack class-template argument, 3 elements");

  holder<int, char, long> h;
  __CPROVER_assert(h.n() == 3, "sizeof...(T) in a member function, 3 elements");
  return 0;
}

// Type requirement: requires { typename T::value_type; }
template<class T>
concept has_value_type = requires { typename T::value_type; };

struct A { using value_type = int; };
struct B {};

template<class T> struct S { static const int x = 0; };
template<has_value_type T> struct S<T> { static const int x = 1; };

int main() {
  __CPROVER_assert(S<A>::x == 1, "A has value_type");
  __CPROVER_assert(S<B>::x == 0, "B has no value_type");
}

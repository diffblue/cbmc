// Basic requires clause on function template — already works (skipped)
template<class T>
  requires (sizeof(T) > 1)
T double_val(T x) { return x + x; }

// Trailing requires clause
template<class T>
T triple_val(T x) requires (sizeof(T) > 1) { return x + x + x; }

// requires clause on partial specialization
template<class T> struct Traits { static const int value = 0; };
template<class T>
  requires (sizeof(T) >= 4)
struct Traits<T*> { static const int value = 1; };

int main()
{
  __CPROVER_assert(double_val(21) == 42, "double_val");
  __CPROVER_assert(triple_val(10) == 30, "triple_val");
  __CPROVER_assert(Traits<int*>::value == 1, "Traits<int*>");
}

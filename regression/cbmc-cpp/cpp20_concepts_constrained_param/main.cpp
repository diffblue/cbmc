// Abbreviated function templates with concept-constrained auto

template<class T>
concept Number = __is_integral(T) || __is_floating_point(T);

// Abbreviated function template: Number auto
Number auto square(Number auto x) { return x * x; }

// Constrained template parameter: template<Number T>
template<Number T>
T cube(T x) { return x * x * x; }

int main()
{
  __CPROVER_assert(square(6) == 36, "square int");
  __CPROVER_assert(cube(3) == 27, "cube int");
}

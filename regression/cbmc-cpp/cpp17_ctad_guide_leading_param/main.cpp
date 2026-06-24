// N5008 [temp.deduct.guide]: a guide deduces its template parameters from the
// matching guide parameters, not positionally from the template parameter list.
// `Vec(int, T) -> Vec<T>` deduces T from the *second* argument, so
// `Vec v{3, x}` with x a char is `Vec<char>`.
//
// Regression: CBMC mapped the first argument onto the template parameter,
// deducing `Vec<int>` and storing without char truncation.
template <typename T>
struct Vec
{
  T val;
  Vec(int, T v) : val(v) {}
};
template <typename T>
Vec(int, T) -> Vec<T>;
int main()
{
  Vec v{3, 'a'};   // guide: Vec<char>
  v.val = 321;     // 321 == 0x141; a char member keeps only the low byte (65)
  __CPROVER_assert(v.val == 65, "guide Vec<char>: 321 truncates to 65");
  return 0;
}

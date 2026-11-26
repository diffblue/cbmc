extern "C" void __CPROVER_assert(bool, const char *);
struct partial_ordering;
enum
{
  partial_category = 0
};
// N5008 [temp.expl.spec]/1: an explicit specialization declares the
// specialization itself; it is no instance of a matching partial
// specialization ([temp.spec.partial.match]).  The MSVC STL's
// _Classify_category (common_comparison_category_t, three_way_comparable)
// has this shape.
template <class...>
constexpr char classify = 9;
template <class T>
constexpr char classify<T> = 1;
template <>
constexpr char classify<partial_ordering> = partial_category;
static_assert(classify<partial_ordering> == 0, "explicit specialization");
int main()
{
  __CPROVER_assert(classify<partial_ordering> == 0, "explicit specialization");
  __CPROVER_assert(classify<int> == 1, "partial specialization");
  __CPROVER_assert(classify<> == 9, "primary template");
  __CPROVER_assert(classify<partial_ordering> == 1, "WRONG (must FAIL)");
  return 0;
}

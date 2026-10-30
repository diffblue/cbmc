// N5008 [expr.comma]/1: the left operand of a comma is a discarded-value
// expression; the type and value of the result are those of the right
// operand.  libstdc++'s <charconv> initializes a static constexpr member
// with `(_DecOnly, _S_make_table())'; its value is the table, and reads of
// its elements are constant expressions ([expr.const]/2).
extern "C" void __CPROVER_assert(bool, const char *);

struct table
{
  int d[3];
};

constexpr table make()
{
  return table{{1, 2, 3}};
}

template <bool B>
struct holder
{
  static constexpr table value = (B, make());
};

template <int N>
struct box
{
  static constexpr int n = N;
};

constexpr table plain = (true, make());

int main()
{
  char a[plain.d[2]];
  __CPROVER_assert(sizeof(a) == 3, "array bound");
  __CPROVER_assert(box<holder<false>::value.d[1]>::n == 2, "template argument");
  __CPROVER_assert(sizeof(a) == 4, "WRONG (must FAIL)");
  return 0;
}

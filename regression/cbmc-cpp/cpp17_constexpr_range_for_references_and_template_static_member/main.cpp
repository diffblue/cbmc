// N5008 [expr.const]/5: a constant expression may modify objects whose
// lifetime began within its evaluation, also through references and
// pointers bound to their subobjects ([stmt.ranged]: `for(auto &e : a)'
// binds e to each element in turn).  [temp.inst]/5: a constexpr member
// function of a class template specialization is instantiated when a
// constant expression needs its value.  This is the shape of libstdc++'s
// __from_chars_alnum_to_val_table<false>::_S_make_table in <charconv>.
extern "C" void __CPROVER_assert(bool, const char *);

template <bool DecOnly>
struct table_of
{
  struct type
  {
    unsigned char data[64] = {};
  };
  static constexpr type make()
  {
    constexpr unsigned char lower[7] = "abcdef";
    type t;
    for(auto &e : t.data)
      e = 127;
    for(int i = 0; i < 10; ++i)
      t.data['0' + i] = i;
    for(int i = 0; i < 6; ++i)
      t.data[lower[i] - 64] = 10 + i;
    return t;
  }
  static constexpr type value = (DecOnly, make());
};

template <int N>
struct sum_of
{
  static constexpr int make()
  {
    int s[N] = {};
    for(int i = 0; i < N; ++i)
      s[i] = i;
    int *p = &s[2];
    *p += 100;
    int total = 0;
    for(const int &x : s)
      total += x;
    return total;
  }
  static constexpr int value = make();
};

int main()
{
  __CPROVER_assert(table_of<false>::value.data['7'] == 7, "digit");
  __CPROVER_assert(table_of<false>::value.data['c' - 64] == 12, "letter");
  __CPROVER_assert(table_of<false>::value.data['/'] == 127, "other");
  __CPROVER_assert(sum_of<5>::value == 110, "write through a pointer");
  __CPROVER_assert(sum_of<5>::value == 10, "WRONG (must FAIL)");
  return 0;
}

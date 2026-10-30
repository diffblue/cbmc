// N5008 [expr.const]: a constexpr function may declare a local of class type
// without an initializer ([basic.indet]/1.2: its bytes are erroneous) and
// assign its array member's elements before reading them; this is the shape
// of libstdc++'s __from_chars_alnum_to_val_table<false>::_S_make_table.
extern "C" void __CPROVER_assert(bool, const char *);

struct table
{
  unsigned char data[64];
};

constexpr table make_uninitialized()
{
  table t;
  for(int i = 0; i < 64; ++i)
    t.data[i] = 127;
  for(int i = 0; i < 10; ++i)
    t.data['0' + i] = i;
  return t;
}

constexpr table make_value_initialized()
{
  table t{};
  for(int i = 0; i < 10; ++i)
    t.data[i] = 2 * i;
  return t;
}

struct holder
{
  static constexpr table value = make_uninitialized();
};

constexpr table plain = make_value_initialized();

int main()
{
  __CPROVER_assert(holder::value.data['7'] == 7, "digit");
  __CPROVER_assert(holder::value.data['!'] == 127, "other");
  __CPROVER_assert(plain.data[9] == 18, "assigned element");
  __CPROVER_assert(plain.data[10] == 0, "value-initialized element");
  __CPROVER_assert(holder::value.data['7'] == 8, "WRONG (must FAIL)");
  return 0;
}

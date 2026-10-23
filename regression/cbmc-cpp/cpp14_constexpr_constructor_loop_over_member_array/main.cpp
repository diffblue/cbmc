extern "C" void __CPROVER_assert(bool, const char *);
// N5008 [basic.start.static]/2, [dcl.constexpr]/6, [expr.const]/5: a
// constexpr variable of class type is constant-initialized; its
// constructor's loop assigning elements of a (multidimensional) member
// array runs at translation time, not at startup, where a loop bound
// would cut it (the MSVC STL's _Digit_pairs in <xutility>)
template <class E>
struct table
{
  E data[100][2];
  constexpr explicit table() : data{}
  {
    for(int i = 0; i != 100; ++i)
    {
      data[i][0] = static_cast<E>('0' + i / 10);
      data[i][1] = static_cast<E>('0' + i % 10);
    }
  }
};
template <class E>
constexpr table<E> pairs{};
constexpr table<char> plain{};
int main()
{
  __CPROVER_assert(pairs<char>.data[42][0] == '4', "variable template");
  __CPROVER_assert(plain.data[99][1] == '9', "variable");
  __CPROVER_assert(plain.data[7][1] == '8', "WRONG (must FAIL)");
}

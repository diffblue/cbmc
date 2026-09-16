extern "C" void __CPROVER_assert(bool, const char *);
typedef unsigned char uint8_t;
template <typename T, uint8_t N, bool W>
struct Outer
{
  template <bool E>
  struct reference
  {
    void on_write();
    int v;
  };
};
template <typename T, uint8_t N, bool W>
template <bool E>
void Outer<T, N, W>::reference<E>::on_write()
{
  v = E ? 1 : 0;
}
int main()
{
  Outer<int, 3, true>::reference<true> r;
  r.v = 5;
  r.on_write();
  __CPROVER_assert(r.v == 1, "nested class template member defined out of class");
  Outer<int, 3, true>::reference<false> f;
  f.on_write();
  __CPROVER_assert(f.v == 0, "second instantiation");
  return 0;
}

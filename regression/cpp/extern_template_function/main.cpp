// Test that extern template function declarations with different
// template arguments generate distinct symbol names.

template <typename T>
struct Wrapper
{
  T val;
};

template <typename T>
const T *get_ptr(int id)
{
  return 0;
}

extern template const Wrapper<char> *get_ptr<Wrapper<char>>(int);
extern template const Wrapper<int> *get_ptr<Wrapper<int>>(int);

int main()
{
  const Wrapper<char> *p1 = get_ptr<Wrapper<char>>(0);
  const Wrapper<int> *p2 = get_ptr<Wrapper<int>>(1);
  return 0;
}

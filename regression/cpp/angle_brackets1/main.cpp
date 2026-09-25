// C++11 right angle bracket fix: >> in nested template arguments
template <typename T>
struct S
{
  typedef T type;
};

// >> should be parsed as two closing angle brackets
typedef S<S<int>> nested;

int main()
{
  nested x;
  return 0;
}

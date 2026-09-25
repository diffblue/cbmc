template <typename T, typename A>
class vec
{
public:
  void reserve(int n);
};

// partial specialization
template <typename A>
class vec<bool, A>
{
public:
  void push_back(bool v);
};

// out-of-class member definition for primary template
// should not be confused with the partial specialization
template <typename T, typename A>
void vec<T, A>::reserve(int n)
{
}

int main()
{
  vec<int, int> v;
  v.reserve(10);
  return 0;
}

// C++11 template parameter packs - parsing test
template <typename... Args>
struct type_list
{
};

template <typename T>
struct wrapper
{
  typedef T type;
};

typedef wrapper<int>::type first_t;

// Non-type template parameter pack
template <int... Values>
struct int_list
{
};

int main()
{
}

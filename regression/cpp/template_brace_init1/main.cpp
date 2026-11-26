// C++11 braced-init-list after template-id: name<args>{}
template <typename T>
struct identity
{
};

template <typename T>
bool check(identity<T>)
{
  return true;
}

template <typename T>
struct S
{
  static_assert(check(identity<T>{}), "msg");
};

int main()
{
  S<int> s;
  identity<int> id = identity<int>{};
  return 0;
}

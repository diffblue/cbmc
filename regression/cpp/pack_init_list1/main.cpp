// C++11: pack expansion in braced-init-list
template <typename... Args>
int first(Args... args)
{
  int arr[] = {args...};
  return arr[0];
}

int main()
{
  return first(0, 1, 2);
}

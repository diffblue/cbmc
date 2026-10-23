// C++11: range-based for in template (parse only)
template <typename T, int N>
int sum(T (&arr)[N])
{
  int s = 0;
  for(auto x : arr)
    s += x;
  return s;
}

int main()
{
  return 0;
}

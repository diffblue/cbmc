// C++11 default template argument for function template
template <typename T = int>
T zero()
{
  return T();
}

int main()
{
  int x = zero();
  __CPROVER_assert(x == 0, "default template arg");
  return 0;
}

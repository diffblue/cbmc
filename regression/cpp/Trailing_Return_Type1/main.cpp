// C++11
// This is an alternative use of the keyword 'auto' and a syntax variant.

auto f00(int x) -> int
{
  return x + 1;
}

class some_class
{
  // as a method

  #if 0
  static auto f002(int x) -> int
  {
    return x + 1;
  }
  #endif
  
  // template function
  template<typename someT>
  static auto f003(int x) -> someT
  {
    return 0;
  }

};

int main()
{
  int i;
  i=f00(1);
}

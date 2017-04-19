template<int I>
class X {
public:
  X()
  {
  }

  static void some_func()
  {
    // This is an unbounded expansion,
    // but is ok, as some_func isn't called.
    X<I-1>::some_func();
  }
};

X<1> x;

int main()
{
  // x.some_func();
}

// also works with function templates
template<typename T>
void some_function_template()
{
  T::MORE_NONSENSE();
}

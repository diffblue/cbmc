// static_assert with const variable and template member
struct S
{
  static const bool stop = false;
};

static_assert(S::stop == false, "non-template");

template <typename T>
struct protector
{
  static const bool stop = false;
};

static_assert(protector<int>::stop == false, "template");

// static_assert inside function body with non-constant expression
template <typename T>
void f()
{
  static_assert(protector<T>::stop == false, "in body");
}

int main()
{
  f<int>();
  return 0;
}

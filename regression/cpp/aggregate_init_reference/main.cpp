// Aggregate initialization of non-POD structs with reference members
struct S
{
  int x;
};

struct T
{
  const S &r;
};

template <typename A>
struct Tag
{
  const A &a;
};

int main()
{
  S s{42};
  T t{s};
  Tag<S> tag = Tag<S>{s};
  return 0;
}

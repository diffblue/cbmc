// C++17 structured bindings with reference qualifier
struct Pair
{
  int first;
  int second;
};

int main()
{
  Pair p{10, 20};

  // Reference binding: modifications through a/b affect p
  auto &[a, b] = p;
  __CPROVER_assert(a == 10, "a reads first");
  __CPROVER_assert(b == 20, "b reads second");

  a = 30;
  __CPROVER_assert(p.first == 30, "ref write through a");

  b = 40;
  __CPROVER_assert(p.second == 40, "ref write through b");

  return 0;
}

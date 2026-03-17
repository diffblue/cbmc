struct S
{
  int x;
  int y;
  friend bool operator==(S, S) = default;
};

bool is_eq(S a, S b)
{
  return a == b;
}

bool is_neq(S a, S b)
{
  return a != b;
}

int main()
{
  S a{1, 2}, b{1, 2}, c{1, 3};
  __CPROVER_assert(is_eq(a, b), "equal");
  __CPROVER_assert(is_neq(a, c), "not equal");
  __CPROVER_assert(!is_neq(a, b), "not not-equal");
}

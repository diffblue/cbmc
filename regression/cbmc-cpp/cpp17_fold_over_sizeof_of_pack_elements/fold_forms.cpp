extern "C" void __CPROVER_assert(bool, const char *);
template <class T, class U>
struct same
{
  static const bool value = false;
};
template <class T>
struct same<T, T>
{
  static const bool value = true;
};
template <class... Ts>
int unary_right(Ts...)
{
  return (static_cast<int>(sizeof(Ts)) + ...);
}
template <class... Ts>
int unary_left(Ts...)
{
  return (... + static_cast<int>(sizeof(Ts)));
}
template <class... Ts>
int binary_right(Ts...)
{
  return (static_cast<int>(sizeof(Ts)) + ... + 100);
}
template <class... Ts>
int weighted(Ts... xs)
{
  // both packs in one pattern, expanded in lockstep ([temp.variadic]/5)
  return (0 + ... + (static_cast<int>(sizeof(Ts)) * xs));
}
template <class... Ts>
bool any_int(Ts...)
{
  return (false || ... || same<Ts, int>::value);
}
template <class... Ts>
int count(Ts...)
{
  return (0 + ... + static_cast<int>(sizeof(Ts)));
}
template <class... Ts>
struct pack
{
  static const int bytes = (0 + ... + static_cast<int>(sizeof(Ts)));
  static const bool any_char = (false || ... || (sizeof(Ts) == 1));
};
int main()
{
  __CPROVER_assert(unary_right('a', 2.0) == 9, "unary right");
  __CPROVER_assert(unary_left('a', 1) == 5, "unary left");
  __CPROVER_assert(binary_right(1, 'b') == 105, "binary right");
  __CPROVER_assert(weighted('\x02', 3) == 2 + 12, "lockstep");
  __CPROVER_assert(any_int('a', 1) && !any_int('a', 2.0), "trait");
  __CPROVER_assert(count() == 0, "empty pack");
  __CPROVER_assert(
    pack<char, int>::bytes == 5 && pack<char, int>::any_char &&
      !pack<int>::any_char,
    "class scope");
  __CPROVER_assert(count(1) == 5, "WRONG (must FAIL)");
}

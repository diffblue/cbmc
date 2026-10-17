extern "C" void __CPROVER_assert(bool, const char *);
struct big
{
  unsigned long v;
  template <class T>
  constexpr big(T i) : v(static_cast<unsigned long>(i))
  {
  }
  friend constexpr bool operator<(const big &l, const big &r)
  {
    return l.v < r.v;
  }
};
big from_int(int i)
{
  return big(i);
}
big from_wide(unsigned __int128 w)
{
  return big(w);
}
bool below_limit(const big &b, unsigned long limit)
{
  // `limit' converts through the constructor template's specialization
  // deduced for unsigned long, not through the ones instantiated above
  // for int and unsigned __int128
  return b < limit;
}
int main()
{
  big a = from_int(5);
  big w = from_wide(7);
  __CPROVER_assert(
    below_limit(a, 6) && !below_limit(w, 7),
    "argument converted by the deduced specialization");
  __CPROVER_assert(below_limit(w, 7), "WRONG (must FAIL)");
}

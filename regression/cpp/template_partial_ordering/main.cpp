// When multiple partial specializations match, the most specialized
// one should be selected. fold<CTp, pack<Rp...>, void> is more
// specialized than fold<CTp, Rp, void> because the second argument
// is constrained to be pack<...>.

template <typename...>
struct pack
{
};

template <typename, typename, typename = void>
struct fold;

template <typename CTp, typename... Rp>
struct fold<CTp, pack<Rp...>, void>
{
  typedef int type;
};

template <typename CTp, typename Rp>
struct fold<CTp, Rp, void>
{
};

int main()
{
  fold<int, pack<long>>::type x = 0;
  return 0;
}

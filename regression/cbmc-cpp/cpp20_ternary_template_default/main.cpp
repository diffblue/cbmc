enum class Kind
{
  sized,
  unsized
};

template <typename T, typename U>
concept sized_sentinel_for = true;

template <
  typename T,
  typename U = T,
  Kind K = sized_sentinel_for<T, U> ? Kind::sized : Kind::unsized>
struct subrange
{
  static constexpr Kind kind = K;
};

int main()
{
  subrange<int> s;
  __CPROVER_assert(s.kind == Kind::sized, "default is sized");
}

// C++20 concepts
template <typename T>
concept Integral = sizeof(T) <= 8;

template <Integral T>
T identity(T x)
{
  return x;
}

int main()
{
  int r = identity(42);
  __CPROVER_assert(r == 42, "concept constrained");
  return 0;
}

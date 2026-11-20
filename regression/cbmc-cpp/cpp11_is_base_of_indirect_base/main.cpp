// N5008 [meta.rel]: is_base_of over indirect bases.
struct A
{
};
struct B : A
{
};
struct C : B
{
};
struct D : C
{
};
struct M : virtual A
{
};
struct N : M
{
};

int main()
{
  static_assert(__is_base_of(A, A), "a type is its own base for is_base_of");
  static_assert(__is_base_of(A, B), "direct");
  static_assert(__is_base_of(A, C), "two levels");
  static_assert(__is_base_of(A, D), "three levels");
  static_assert(__is_base_of(B, D), "middle");
  static_assert(__is_base_of(A, N), "through a virtual base");
  static_assert(!__is_base_of(D, A), "not the other way");
  static_assert(!__is_base_of(B, M), "unrelated");
  return 0;
}

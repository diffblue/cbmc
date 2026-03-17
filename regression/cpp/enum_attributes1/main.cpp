// C++11 attributes on enumerators and multiple GCC attributes
enum E
{
  A __attribute__((unused)),
  B __attribute__((unused)) = 5
};

int main()
{
  E e = A;
  int x = B;
  return 0;
}

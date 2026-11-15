enum class E
{
  a,
  b
};
void f(int);
int main()
{
  // [dcl.enum]/10: no implicit conversion of a scoped enumeration
  f(E::b);
  return 0;
}

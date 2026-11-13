// Lambda with trailing return type including pointer/reference qualifiers
// Tests that rTypeName is used (not rTypeSpecifier) for trailing return types
template <class T>
struct S
{
  T val;
  S(S &&other)
    : val([](S &s) -> T & { return s.val; }(other))
  {
  }
};
int main()
{
  return 0;
}

template <class T>
int f(T, int)
{
  return 1;
}
namespace n
{
template <class T>
int f(T)
{
  return 2;
}
// ::f is hidden by n::f ([basic.lookup.unqual]/1), so the call has no
// viable candidate and the program is ill-formed
int g()
{
  return f<int>(0, 0);
}
} // namespace n
int main()
{
  return n::g();
}

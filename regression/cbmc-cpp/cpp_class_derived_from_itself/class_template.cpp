// [class.derived.general]/2: S<int> is incomplete in its own
// base-specifier-list
template <class T>
struct S : S<T>
{
};
int main()
{
  S<int> s;
}

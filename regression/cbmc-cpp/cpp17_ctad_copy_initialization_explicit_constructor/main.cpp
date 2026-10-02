// [over.match.class.deduct]/1, [over.match.copy]/1.1: in copy-initialization
// the guide formed from an explicit constructor is not a candidate, so
// `E e = 1;' has no viable guide and is ill-formed
template <class T>
struct E
{
  T v;
  explicit E(T t) : v(t)
  {
  }
};
int main()
{
  E e = 1;
  return e.v;
}

// N5008 [over.match.class.deduct]/3-4: T cannot be both int and long.
template <class T, class U>
struct P
{
  T a;
  U b;
};
template <class T>
using same = P<T, T>;
int main()
{
  same s{1, 2L}; // T deduced as both int and long
  return s.a;
}

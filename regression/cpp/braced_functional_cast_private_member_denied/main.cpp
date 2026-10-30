// N5008 [class.access.general]/6: other::hidden is private, also in T{...}.
#include <initializer_list>
struct V
{
  int f;
  V(std::initializer_list<int> l) : f(*l.begin())
  {
  }
};
struct other
{
private:
  int hidden = 1;
};
int peek(other &o)
{
  return V{o.hidden, 3}.f; // other::hidden is private here
}
int main()
{
  other o;
  return peek(o);
}

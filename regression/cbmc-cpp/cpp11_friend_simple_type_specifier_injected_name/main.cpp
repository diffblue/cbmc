// N5008 [class.friend]/3, /11: a friend declaration with a
// simple-type-specifier (`friend G<vector>;') names an existing class by
// ORDINARY lookup from the class scope, where the injected-class-name
// `vector' denotes the current specialization ([temp.local]/1).  Only an
// unqualified elaborated-type-specifier (`friend class B;') is looked up in
// the innermost enclosing namespace.  MSVC's <vector>:
// `friend _Tidy_guard<vector>;'.
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct guard
{
  T *target;
  int peek() const
  {
    return target->x;
  }
};
template <class T>
class vector
{
  template <class>
  friend class other;
  friend guard<vector>;
  int x;

public:
  vector() : x(1)
  {
  }
  int get() const
  {
    return x;
  }
};
class B;
class holder
{
  friend class B;
  int secret = 7;
};
class B
{
public:
  int read(const holder &h)
  {
    return h.secret;
  }
};
int main()
{
  vector<int> v;
  guard<vector<int>> g{&v};
  __CPROVER_assert(g.peek() == 1, "friend by simple-type-specifier");
  __CPROVER_assert(v.get() == 1, "member");
  holder h;
  __CPROVER_assert(B().read(h) == 7, "friend class");
  return 0;
}

#define DEF_INSIDE

template<class T>
class my_template {
  T m;
public:
  my_template() : m(0) {}
  my_template(T _m) : m(_m) {}

// TODO: doesn't work
//  my_template(T _m) { m = _m; }

  void set(T _m) { m = _m; }
#ifdef DEF_INSIDE
  T get() { return m; }
#else
  T get();
#endif
};

#ifndef DEF_INSIDE
template<class T>
T my_template<T>::get()
{
  return m;
}
#endif


int main (int argc, char *argv[])
{
  my_template<unsigned char> z(3);
  my_template<int> x;
  x.set(5);
  int y = x.get();
  __CPROVER_assert(y == 5, "");
  __CPROVER_assert(z.get() == 3, "");

  return 0;
}

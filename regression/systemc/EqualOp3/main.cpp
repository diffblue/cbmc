template<class T>
class myclass2;

template<class T>
class myclass
{
public:
  myclass(T _m) : m(_m) {}

// TODO: doesn't work
//  myclass<T> &operator= (const myclass<T> &e) { m = e.m+2; return *this; }
//  myclass<T> operator= (myclass2<T> e) { m = e.m+2; return *this; }
//  bool operator== (myclass<T> e) { return (m == e.m); }

  T m;
};

template<class T>
class myclass2
{
public:
  myclass2(T _m) : m(_m) {}

  myclass2<T> operator= (myclass<T> e) { m = e.m+2; return *this; }

// TODO: doesn't work
//  myclass2<T> operator= (myclass2<T> e) { m = e.m+2; return *this; }

  bool operator== (myclass<T> e) { return (m == e.m); }

  T m;
};

int main(int argc, char** argv)
{
  myclass2<int> x(0);
  myclass<int> y(1);
  x = y;
  __CPROVER_assert(x == y, "");
  return 0;
}

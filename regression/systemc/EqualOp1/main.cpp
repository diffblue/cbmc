template<class T>
class myclass
{
public:
  myclass(T _m) : m(_m) {}

  myclass<T> operator= (myclass<T> e);

protected:
  T m;
};

template<class T>
myclass<T> myclass<T>::operator= (myclass<T> e) { m = e.m; return *this; }

int main(int argc, char** argv)
{
  myclass<int> x(0);
  myclass<int> y(1);
  x = y;
  __CPROVER_assert(x == y, "");
}

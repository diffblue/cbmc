#include <cassert>

struct A
{
    int i;
    A():i(10){}

  private:
    A(const A& a); // disabled
};

template <class T>
class B:  A {
  public:
    T t;
    B(){};
    int get_i(){return i;}
  private:
    B(B<T>& b); // disabled
};


template <>
class B<bool>:  A {
  public:
    bool b;
    B():b(true){};
    int get_i(){return i;}
  private:
    B(B<bool>& b); // disabled
};


B<int> b1;
int main()
{
  assert(b1.t == 0);
  B<bool> b2;
  assert(b2.b == true);
}

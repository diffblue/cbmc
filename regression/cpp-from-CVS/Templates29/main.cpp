namespace N {
template <class T>
struct A
{
  T i;
  A(T i):i(i){}
};
}

struct B : N::A<int>
{
  B(int i): N::A<int>(i) {}
  void  func(){};
  int b;
};

int main()
{
  B b(10);
  assert(b.i == 10);
}

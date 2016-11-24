template <class T1>
struct A
{
  T1 t;

  template <class T2>
  void set(T2 t){ this->t = t; }

};

int main()
{
  A<bool> a;
  a.set<int>(0);
  assert(a.t == false);
};

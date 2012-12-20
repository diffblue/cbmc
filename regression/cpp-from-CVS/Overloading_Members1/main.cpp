class T
{
public:
  int f() const
  {
    return 1;
  }

  int f()
  {
    return 2;
  }
};

int main()
{
  T x;
  const T x_const;

  assert(x_const.f()==1);
  assert(x.f()==2);
}

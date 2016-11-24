
template <int c1>
struct A
{
  int func(){return c1;}
};

template <int c1, int c2>
struct B
{
  A<c1*2+c2> a;
};

int main()
{
  B<5,4> b;
  assert(b.a.func() == 14);
}

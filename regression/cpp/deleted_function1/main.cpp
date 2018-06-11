class A
{
public:
  void foo() {}
};

class B : public A
{
public:
  void foo() = delete;
};

int main()
{
  B b;
  b.foo();

  return 0;
}

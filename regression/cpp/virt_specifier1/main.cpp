// C++11 final on class declarations and override/final on member functions
struct Base
{
  virtual void f();
  virtual void g();
  virtual void h();
};

struct Derived final : public Base
{
  void f() override;
  void g() final;
  void h() override final;
};

int main()
{
  Derived d;
  return 0;
}

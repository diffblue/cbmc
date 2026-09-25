// C++11: override and final on destructors
struct Base
{
  virtual ~Base() noexcept;
};
struct Derived : Base
{
  ~Derived() noexcept override;
};
struct Final : Base
{
  ~Final() noexcept final;
};
int main()
{
  return 0;
}

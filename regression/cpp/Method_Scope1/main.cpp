class Base
{
public:
  typedef int my_t;
};


class Derived : public Base
{
protected:
  void m01();
  void m00(my_t message);
};


// Should work
void Derived::m00(my_t message)
{
  return;
}

int main()
{
}

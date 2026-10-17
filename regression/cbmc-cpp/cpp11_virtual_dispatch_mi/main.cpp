// Mirrors the VmsStateMachines pattern: multiple base classes, qualified call
// into one base's non-virtual method which calls a pure virtual on `this`.

#include <cassert>

struct B0
{
  virtual bool f0() = 0;
};
struct B1
{
  virtual bool f1() = 0;
};
struct B2
{
  virtual bool f2() = 0;
};
struct B3
{
  virtual bool f3() = 0;
};
struct B4
{
  virtual bool f4() = 0;
};
struct B5
{
  virtual bool f5() = 0;
};
struct B6
{
  virtual bool f6() = 0;
};
struct B7
{
  virtual bool f7() = 0;
};
struct B8
{
  virtual bool guard() = 0;
  bool eval()
  {
    return guard();
  }
};

struct Concrete : B0, B1, B2, B3, B4, B5, B6, B7, B8
{
  bool value;
  bool f0() override
  {
    return false;
  }
  bool f1() override
  {
    return false;
  }
  bool f2() override
  {
    return false;
  }
  bool f3() override
  {
    return false;
  }
  bool f4() override
  {
    return false;
  }
  bool f5() override
  {
    return false;
  }
  bool f6() override
  {
    return false;
  }
  bool f7() override
  {
    return false;
  }
  bool guard() override
  {
    return value;
  }

  bool run()
  {
    return B8::eval();
  } // qualified call — triggers the bug
};

int main()
{
  Concrete c;
  c.value = true;
  assert(c.run() == true);
  return 0;
}

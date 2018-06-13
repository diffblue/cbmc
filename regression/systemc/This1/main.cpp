#include <cassert>

class Foo;

class Bar
{
public:
  Bar(Foo* fp) : fooptr(fp) {}
  //inline
  void Set(int);
  Foo* fooptr;
};

class Foo
{
public:
  //inline
  Bar bar() {
    return Bar(this);
  }
  int value;
};

//inline
void Bar::Set(int new_value)
{
  fooptr->value = new_value;
}

int main(void)
{
  Foo x;
  x.bar().Set(42);
  assert(x.value == 42);
  x.bar().Set(99);
  assert(x.value == 99);
}

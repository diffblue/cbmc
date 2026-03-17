#include <cassert>

struct Movable
{
  int *data;
  bool moved;

  Movable() : data(new int(42)), moved(false)
  {
  }
  Movable(Movable &&other) : data(other.data), moved(false)
  {
    other.data = 0;
    other.moved = true;
  }
  Movable &operator=(Movable &&other)
  {
    if(this != &other)
    {
      delete data;
      data = other.data;
      other.data = 0;
      other.moved = true;
    }
    return *this;
  }
  ~Movable()
  {
    delete data;
  }

  // Delete copy
  Movable(const Movable &) = delete;
  Movable &operator=(const Movable &) = delete;
};

int main()
{
  Movable a;
  assert(*a.data == 42);

  Movable b(static_cast<Movable &&>(a));
  assert(a.moved);
  assert(a.data == 0);
  assert(*b.data == 42);

  return 0;
}

// A class that is a friend of the member's type may default-initialize a
// member whose default constructor is otherwise private
// (class.access.base): this must be accepted.

#include <cassert>

struct holder;

struct m
{
  int v;

private:
  m() : v(7)
  {
  }
  friend struct holder;
};

struct holder
{
  m field;
  holder()
  {
  }
  int get() const
  {
    return field.v;
  }
};

int main()
{
  holder h;
  assert(h.get() == 7);
  return 0;
}

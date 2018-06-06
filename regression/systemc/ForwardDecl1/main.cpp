#include <cassert>

#define INSIDE

class sc_uint_subref;

class sc_uint_base
{
 friend class sc_uint_subref;

 public:
  sc_uint_base(unsigned long v)
    : val(v)
  {
  }

  sc_uint_subref range(int left, int right)
#ifndef INSIDE
  ;
#else
  {
    return sc_uint_subref(this, left, right);
  }
#endif

 protected:
  unsigned long val;
};

class sc_uint_subref
{
 friend class sc_uint_base;

 public:
  sc_uint_subref() {}
  sc_uint_subref(sc_uint_base *_ptr, int _left, int _right)
    : left(_left), right(_right), ptr(_ptr)
  {}

  bool operator==(const sc_uint_base &other)
  {
    return ptr->val == other.val;
  }

  sc_uint_subref &operator=(const sc_uint_subref &other)
  {
    ptr = other.ptr;
    left = other.left;
    right = other.right;
    return *this;
  }

 protected:
  int left, right;
  sc_uint_base *ptr;

};

#ifndef INSIDE
sc_uint_subref sc_uint_base::range(int left, int right)
{
  return sc_uint_subref(this, left, right);
}
#endif

int main(int argc, char** argv)
{
  sc_uint_base x(42);
  sc_uint_subref y = x.range(0,5);

  assert(y == x);

  return 0;
}

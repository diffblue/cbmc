// Per [expr.new] and [expr.delete]: non-array new-expression allocates
// storage and constructs an object; delete-expression destroys the
// object and deallocates the storage.

struct counted
{
  static int ctor_count;
  static int dtor_count;
  int v;
  counted(int v_) : v(v_)
  {
    ++ctor_count;
  }
  ~counted()
  {
    ++dtor_count;
  }
};

int counted::ctor_count = 0;
int counted::dtor_count = 0;

int main()
{
  // new T(args): allocate + construct
  counted *p = new counted(17);
  __CPROVER_assert(counted::ctor_count == 1, "new ran constructor");
  __CPROVER_assert(p->v == 17, "argument passed to constructor");

  // delete p: destroy + deallocate
  delete p;
  __CPROVER_assert(counted::dtor_count == 1, "delete ran destructor");

  return 0;
}

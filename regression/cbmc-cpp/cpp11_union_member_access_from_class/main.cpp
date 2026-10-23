// N5008 [class.union.general]/3: a union has no base classes.  The access
// check for a PRIVATE member reached through a UNION object from a member of
// another class (a friend, [class.friend]) asked "is the enclosing class
// derived from the union?", which requires a struct type and aborted
// (to_struct_type precondition) -- libc++ std::variant's storage `__union'
// (private __head/__tail) read by its friend `__access::__union::__get_alt'.
extern "C" void __CPROVER_assert(bool, const char *);
struct Access;
union Storage
{
public:
  Storage() : i(0)
  {
  }
  friend struct Access;

private:
  int i;
  double d;
};
struct Access
{
  template <class U>
  static int &get_int(U &u)
  {
    return u.i;
  }
  static double &get_double(Storage &s)
  {
    return s.d;
  }
};
class Holder
{
  Storage s;

public:
  int read()
  {
    return Access::get_int(s);
  }
  void set(double v)
  {
    Access::get_double(s) = v;
  }
  double read_double()
  {
    return Access::get_double(s);
  }
};
int main()
{
  Holder h;
  __CPROVER_assert(h.read() == 0, "union member through class");
  h.set(2.5);
  __CPROVER_assert(h.read_double() == 2.5, "union member written");
  __CPROVER_assert(h.read_double() == 1.5, "WRONG (must FAIL)");
}

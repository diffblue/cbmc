extern "C" void __CPROVER_assert(bool, const char *);
namespace lib
{
class data
{
  int id = 0;
  friend void set_id(data *, int);
  friend int get_id(const data &);

public:
  // the friends are called before their definitions below
  void reset()
  {
    set_id(this, 0);
  }
};
class factory
{
public:
  data make(int id) const;
};
data factory::make(int id) const
{
  data d;
  set_id(&d, id);
  return d;
}
void set_id(data *d, int id)
{
  d->id = id;
}
int get_id(const data &d)
{
  return d.id;
}
} // namespace lib
int main()
{
  lib::factory f;
  lib::data d = f.make(4);
  __CPROVER_assert(get_id(d) == 4, "set by the friend");
  d.reset();
  __CPROVER_assert(get_id(d) == 0, "reset");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

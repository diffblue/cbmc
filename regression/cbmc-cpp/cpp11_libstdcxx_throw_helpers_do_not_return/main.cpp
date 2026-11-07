// libstdc++ declares its exception helpers std::__throw_X
// __attribute__((__noreturn__)) and defines them in its compiled library
// (functexcept.cc): each throws an X.  libstdc++ 16's
// __new_allocator::allocate is `if(n > max_size()) __throw_bad_alloc();
// else return ...;', so a call taken to return falls off the end of the
// function ([stmt.return]/4: undefined behaviour) with an arbitrary result.
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" unsigned nondet_unsigned();
namespace std
{
class exception
{
public:
  virtual ~exception()
  {
  }
};
class bad_alloc : public exception
{
};
class length_error : public exception
{
public:
  explicit length_error(const char *)
  {
  }
};
void __throw_bad_alloc() __attribute__((__noreturn__));
void __throw_length_error(const char *) __attribute__((__noreturn__));
} // namespace std
int storage[4];
int *allocate(unsigned n)
{
  if(n > 4)
    std::__throw_bad_alloc();
  else
    return storage;
}
int checked(unsigned n)
{
  if(n == 0)
    std::__throw_length_error("empty");
  return 1;
}
int main()
{
  const unsigned n = nondet_unsigned();
  bool returned = false, thrown = false, length = false;
  try
  {
    int *p = allocate(n);
    returned = p == storage && n <= 4;
  }
  catch(const std::bad_alloc &)
  {
    thrown = n > 4;
  }
  try
  {
    checked(n);
  }
  catch(const std::length_error &)
  {
    length = n == 0;
  }
  __CPROVER_assert(returned || thrown, "returned or thrown");
  __CPROVER_assert(n != 0 || length, "length_error thrown");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

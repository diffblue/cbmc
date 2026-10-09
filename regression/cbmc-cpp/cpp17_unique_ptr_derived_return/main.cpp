// Dog-food kernel (src/util/timestamper.cpp): a factory whose switch
// returns unique_ptr<const Derived>(new Derived()) from a function
// declared to return unique_ptr<const Base> must use unique_ptr's
// converting move constructor ([unique.ptr.single.ctor]/26,
// unique_ptr<U,E> with U* convertible to T*).  CBMC rejects the
// return conversion ("invalid implicit conversion from 'struct
// unique_ptr' to 'struct unique_ptr'").  The plain if-based sibling
// with virtual members verifies (k2 negative result) -- the switch
// with two differently-typed returns is load-bearing.
#include <memory>
extern "C" void __CPROVER_assert(bool, const char *);
struct timestampert
{
  enum class clockt
  {
    NONE,
    MONOTONIC
  };
  virtual ~timestampert() = default;
  virtual int kind() const
  {
    return 0;
  }
};
struct monotonic_timestampert : public timestampert
{
  int kind() const override
  {
    return 1;
  }
};
std::unique_ptr<const timestampert> make(timestampert::clockt c)
{
  switch(c)
  {
  case timestampert::clockt::NONE:
    return std::unique_ptr<const timestampert>(new timestampert());
  case timestampert::clockt::MONOTONIC:
    return std::unique_ptr<const monotonic_timestampert>(
      new monotonic_timestampert());
  }
  return nullptr;
}
int main()
{
  __CPROVER_assert(
    make(timestampert::clockt::MONOTONIC)->kind() == 1,
    "factory returns derived through base unique_ptr");
  return 0;
}

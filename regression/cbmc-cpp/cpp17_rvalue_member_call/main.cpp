// Regression: rvalue-receiver method dispatch
// (`std::move(receiver).method()`) per [class.this] /
// [over.match.funcs]/3.
//
// Reduced from dog-fooding goto-cc on src/util/type.h:103
//
//   typet &&with_source_location(const typet &type) &&
//   {
//     return std::move(*this).with_source_location(type.source_location());
//   }
//
// The recursive call binds the implicit object parameter of an
// `&&`-qualified member function to `std::move(*this)` (an
// xvalue).  CBMC's reference_binding incorrectly applied the
// "xvalue cannot bind to non-const lvalue ref" rule to the
// implicit `this` parameter (which is internally encoded as an
// lvalue ref to a pointer), rejecting every `&&`-qualified
// member function as inapplicable.  The error reads
//
//   found no match for symbol 'method'
//
// even though g++ accepts the same code.

#include <utility>

struct sloc
{
};

class typet
{
public:
  typet &&with_source_location(sloc) &&
  {
    return std::move(*this);
  }
  typet &with_source_location(sloc) &
  {
    return *this;
  }
  typet &&with_source_location(const typet &t) &&
  {
    sloc s;
    return std::move(*this).with_source_location(s);
  }
  typet &with_source_location(const typet &t) &
  {
    return *this;
  }
};

int main()
{
  typet t;
  std::move(t).with_source_location(typet{});
  return 0;
}

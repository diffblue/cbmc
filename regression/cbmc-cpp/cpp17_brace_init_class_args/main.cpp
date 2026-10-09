// Regression for [over.match.list] viability + conversion of
// brace-init operands to class-typed (and reference-to-class)
// constructor parameters.
//
// The motivating pattern, from CBMC's own `irept` (see
// `src/util/type.h:38`):
//
//   typet(irep_idt _id, typet _subtype)
//     : irept(std::move(_id), {}, {std::move(_subtype)})
//   {}
//
// where `irept`'s ctor takes
//   `(irep_idt, named_listt const&, sub_listt const&)`,
// and the second parameter receives empty `{}` while the third
// receives non-empty `{x}`.
//
// Before the fix, `cpp_typecheck_fargst::match` rejects the
// candidate with "found no match for symbol 'ireptish'" because
// neither brace-init operand was admitted as a viable conversion
// against a class-typed reference parameter.

#include <initializer_list>
#include <utility>

struct dstringt
{
  dstringt()
  {
  }
};

struct named_listt
{
  named_listt()
  {
  }
  named_listt(std::initializer_list<int>)
  {
  }
};

struct sub_listt
{
  sub_listt()
  {
  }
  sub_listt(std::initializer_list<int>)
  {
  }
};

struct ireptish
{
  ireptish()
  {
  }
  ireptish(const dstringt &, const named_listt &, const sub_listt &)
  {
  }
};

struct typetish : ireptish
{
  typetish()
  {
  }
  typetish(dstringt _id, int _subtype)
    : ireptish(std::move(_id), {}, {_subtype})
  {
  }
};

int main()
{
  dstringt d;
  typetish t(d, 42);
  return 0;
}

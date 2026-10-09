// `auto &&r = l;` with l a const lvalue: [dcl.type.auto.deduct]/4
// deduces via the forwarding-reference rule of [temp.deduct.call]/3,
// so auto = const listt& and reference collapsing yields const listt&.
// CBMC instead deduces auto = const listt and then rejects binding the
// lvalue: "invalid implicit conversion from 'const struct listt' to
// 'const struct listt &&'".  The same defect breaks any function
// template taking a forwarding reference called with a const lvalue
// (goto_program.h's for_each_instruction_if instantiated from
// restrict_function_pointers.cpp -- `auto &&instructions =
// goto_function.body.instructions`).
extern "C" void __CPROVER_assert(bool, const char *);

struct listt
{
  int head;
};

int main()
{
  const listt l{42};
  auto &&r = l;
  __CPROVER_assert(r.head == 42, "auto&& binds a const lvalue");
  return 0;
}

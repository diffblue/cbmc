// C++ typeid / RTTI (N5008 [expr.typeid], [type.info])
#include <typeinfo>

int main()
{
  // typeid yields a const std::type_info lvalue; two type_info objects
  // compare equal iff they denote the same type.
  const std::type_info &a = typeid(int);
  const std::type_info &b = typeid(int);
  const std::type_info &c = typeid(char);

  int x = 0;

  // Same type compares equal.
  __CPROVER_assert(typeid(int) == typeid(int), "same type equal");
  __CPROVER_assert(a == b, "same type via references equal");

  // Different types compare unequal.
  __CPROVER_assert(typeid(int) != typeid(char), "different types unequal");
  __CPROVER_assert(!(a == c), "int and char unequal");

  // The expression form uses the static type of its (unevaluated) operand.
  __CPROVER_assert(
    typeid(x) == typeid(int), "expression form uses static type");

  // typeid ignores top-level cv-qualifiers and references ([expr.typeid]/5).
  const int &rx = x;
  __CPROVER_assert(typeid(rx) == typeid(int), "cv/ref ignored");

  // The type_info object is unique per type.
  __CPROVER_assert(&a == &b, "unique per type");

  return 0;
}

// C++20 requires-expression soft-failure ([expr.prim.req.general]/5): a
// requirement whose expression is invalid in the immediate context makes the
// enclosing requires-expression evaluate to *false* -- it is not an ill-formed
// program.  This must hold even when the invalid expression uses an overloaded
// operator on a class type, or a member access, whose resolution would
// otherwise emit a hard diagnostic.

struct NoPlus
{
};

struct HasFooMember
{
  void foo();
};

// simple-requirement using a (missing) overloaded operator on a class type.
template <class T>
concept Addable = requires(T a) { a + a; };

// simple-requirement using a member call.
template <class T>
concept HasFoo = requires(T a) { a.foo(); };

int main()
{
  // operator+ exists for int but not for NoPlus -> soft false, not an error.
  static_assert(Addable<int>, "int is addable");
  static_assert(!Addable<NoPlus>, "NoPlus has no operator+");

  // member foo() exists for HasFooMember but not for int (a non-class type:
  // member access would otherwise be a hard error) -> soft false.
  static_assert(HasFoo<HasFooMember>, "HasFooMember has foo()");
  static_assert(!HasFoo<int>, "int has no member foo()");

  return 0;
}

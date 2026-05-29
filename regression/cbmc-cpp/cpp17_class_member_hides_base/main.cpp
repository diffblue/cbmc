// Regression for [class.member.lookup]/4 hiding rule applied to ADL.
//
// CBMC's `resolve_with_arguments` (the ADL implementation) adds members
// of an argument's class scope to the candidate set.  Per
// [basic.lookup.argdep]/4, only friends declared inside the associated
// class participate in ADL — but a strict implementation of that rule
// breaks files that depend on the broader behaviour for member-template
// resolution.  The principled compromise is to keep the broad gathering
// step but apply [class.member.lookup]/4 hiding to the combined
// candidate set: a same-named member declared in a derived class hides
// the inherited base-class member.
//
// Without that filter, calling an unqualified static method from inside
// a derived class — when the same name exists in a base class with
// matching signature — produces a spurious "does not uniquely resolve"
// ambiguity.  This pattern shows up in CBMC's own `std_expr.h` where
// `nullary_exprt::validate` calls `check(expr, vm)` and `check` is
// defined in both `nullary_exprt` and the base `exprt`.

struct exprt
{
  static void check(const exprt &, int = 0) {}
};

struct expr_protectedt : public exprt
{
};

struct nullary_exprt : public expr_protectedt
{
  // Same signature as exprt::check.  Per [class.member.lookup]/4 this
  // hides exprt::check when looking up `check` from inside
  // nullary_exprt.
  static void check(const exprt &expr, int vm = 0)
  {
    (void)expr;
    (void)vm;
  }

  static void validate(const exprt &expr, int vm = 0)
  {
    // Unqualified call.  Resolution must yield nullary_exprt::check,
    // not the inherited exprt::check, despite the parameter `expr`'s
    // type matching the declaring class of the inherited overload.
    check(expr, vm);
  }
};

int main()
{
  exprt e;
  nullary_exprt::validate(e);
  return 0;
}

// Regression for three related fixes to operator-overload resolution:
//
// 1. `cpp_typecheck_resolvet::resolve_with_arguments` (the ADL /
//    Koenig-lookup pass) terminated its enclosing-namespace walk at
//    `is_root_scope()`, so a free operator declared at global scope
//    on a class declared at global scope (e.g.,
//    `bool operator<(const BigInt &, const BigInt &)` in
//    `bigint.hh`) was not found via ADL when an unqualified-but-
//    shadowed lookup (e.g., inside the body of an unrelated
//    `operator<` member function) failed to locate it via the
//    regular scope walk.  [basic.lookup.argdep]/2 says the
//    associated namespaces of a class type include the namespace of
//    which the class is a member; for a globally-declared class,
//    that namespace IS the root namespace.
//
// 2. `cpp_typecheckt::operator_is_overloaded`'s 1st-option path
//    (member operator) used `resolve` with recursive name lookup,
//    so a free `operator@` declared at file scope was returned
//    when T1 had only `operator@=` (and no `operator@`) as a
//    member.  The downstream synthesis of `a.operator@(b)` was
//    malformed and the 2nd-option (free-function) path was never
//    reached.  Pre-check that T1 declares the operator as a member
//    before entering the 1st-option path.
//    [over.match.oper]/3.2: the SET OF MEMBER CANDIDATES is the
//    result of a qualified lookup `T1::operator@`.
//
// 3. `cpp_typecheckt::operators[]` (the table that drives
//    `operator_is_overloaded`) was missing entries for the modulo
//    operator `%` (`ID_mod`).  As a result, `a % b` for `a` and
//    `b` of class type with a free `operator%(const T &,
//    const T &)` was not even considered for overload resolution,
//    falling straight through to the C-level built-in modulo
//    which then rejected it with
//      conversion from 'const struct T' to 'struct T':
//      implicit arithmetic conversion not permitted.
//
// 4. `operator_is_overloaded`'s 2nd-option (free-function) path
//    selected the user-defined `operator<<(const BigInt &,
//    const BigInt &)` for an arithmetic operand pair like
//    `1UL << some_enum_const` because `BigInt` has implicit ctors
//    from arithmetic types.  Per [over.match.oper]/3.4 (last
//    paragraph): if no operand has class type, the non-member
//    candidate set is restricted to operators whose first or
//    second parameter type is the enumeration operand type itself.
//    A free operator on an unrelated class type (e.g., BigInt) is
//    NOT a candidate; the built-in operator (with an integral
//    promotion of the enum operand) IS the unique winner.
//
// All four fixes together unblock typecheck of `mp_arith`-style
// libstdc++-using files that include `<wctype.h>` (where
// `_ISwbit(__ISwupper)` expands to `(int)((1UL << 0) << 24)` and
// `__ISwupper` is an enum constant).

struct BigInt
{
  int x;
  BigInt() : x(0)
  {
  }
  BigInt(int) : x(0)
  {
  }
  BigInt(unsigned long) : x(0)
  {
  }
  int compare(const BigInt &) const
  {
    return 0;
  }
  BigInt &operator%=(const BigInt &)
  {
    return *this;
  }
};

inline bool operator<(const BigInt &lhs, const BigInt &rhs)
{
  return lhs.compare(rhs) < 0;
}

inline BigInt operator%(const BigInt &lhs, const BigInt &rhs)
{
  return BigInt(lhs) %= rhs;
}

// ADL fix: free operator< at global scope, used inside body of an
// unrelated `operator<` member function.
class rationalt
{
  BigInt numerator;

public:
  rationalt() : numerator(0)
  {
  }
  bool operator<(const rationalt &n) const
  {
    return numerator < n.numerator;
  }
};

// 1st-option-skip fix: free operator% at global scope, used between
// two BigInt values when only operator%= is a member.
BigInt mod(const BigInt &a, const BigInt &b)
{
  return a % b;
}

// [over.match.oper]/3.4 fix: 1UL << enum_const must use built-in
// shift, not the user-defined operator<<(BigInt, BigInt).
enum E
{
  Y0 = 0,
};

inline BigInt operator<<(const BigInt &, const BigInt &)
{
  return BigInt();
}

enum
{
  X = (int)((1UL << Y0) << 24),
};

int main()
{
  rationalt r1, r2;
  bool b = r1 < r2;
  BigInt a, c;
  BigInt m = a % c;
  (void)b;
  (void)m;
  return X != (1 << 24) ? 1 : 0;
}

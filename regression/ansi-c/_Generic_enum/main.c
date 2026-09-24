// _Generic matching is by C11 compatibility. GCC and Clang do not treat an
// enumerated type as compatible with a plain `int` controlling expression (or
// vice versa) for the purpose of generic selection: such a controlling
// expression falls through to `default`. This pins that CBMC behaves the same,
// since matching now goes through gcc_types_compatible_p (which otherwise
// relates an enum to its underlying integer type).
//
// Note: CBMC's _Generic parser does not accept an inline `enum E :`
// association, so the enumerated type is referred to via a typedef.

enum E
{
  A
};
typedef enum E enumE;

int main(void)
{
  int i = 0;
  // int controlling expression does not match the enum arm -> default.
  _Static_assert(_Generic(i, enumE : 1, default : 2) == 2, "int -> default");

  enumE e = A;
  // enum controlling expression does not match the int arm -> default.
  _Static_assert(_Generic(e, int : 1, default : 2) == 2, "enum -> default");

  // an enum controlling expression matches its own enum arm.
  _Static_assert(_Generic(e, enumE : 3, default : 2) == 3, "enum -> enum");

  (void)i;
  (void)e;
  return 0;
}

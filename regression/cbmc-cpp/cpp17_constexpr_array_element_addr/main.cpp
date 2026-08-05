// N5008 [dcl.constexpr]/1 + [expr.sub] + [expr.unary.op]/3: a constexpr
// ARRAY variable is still an object; its elements are lvalues whose
// address can be taken.  CBMC lowered every constexpr variable to a
// fold-away macro, so libc++ <charconv>'s
//   copy_n(&__digits_base_10[__value * 2], 2, p)   (__itoa::__append2)
// became address-of an array LITERAL: "address_of error: ... not an
// lvalue", killing <vector>/<map> conversions seeded from
// preprocessed source.  The object identity AND the initializer value
// must both survive (the first fix attempt kept the symbol but lost
// the static initialization -- the assertion below caught it).
extern "C" void __CPROVER_assert(bool, const char *);
inline constexpr char digits[4] = {'a', 'b', 'c', 'd'};
char *copy1(const char *src, char *dst) { *dst = *src; return dst + 1; }
char *append2(char *p, unsigned v) {
  return copy1(&digits[v * 2], p);
}
int main() {
  char buf[2];
  append2(buf, 1);
  __CPROVER_assert(buf[0] == 'c', "digit table");
  return 0;
}

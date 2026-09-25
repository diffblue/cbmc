// N5008 [dcl.init.aggr]/3.1, /5.1: in a designated-initializer-list the
// explicitly initialized elements are the members the designators NAME; every
// other element is initialized from its default member initializer.  The
// front end filled default member initializers by COUNT ("the first N members
// were given"), so `{.c = 7}` on `struct {int a=1; int b=2; int c=3;}` left
// a=0 and dropped 7 -- wrong verdicts.  A braced default member initializer
// of a bit-field (`uint16_t b : 1 {false}`, libc++'s __format::__fields)
// reached the model as a raw initializer_list cast to the bit-field, which
// aborted the bit-vector flattener ("Reached unimplemented
// boolbv_widtht::get_entry()") -- the shape of `inline constexpr __fields
// __fields_bool{.__type_ = true}` behind every libc++ <format>/<span> test.
extern "C" void __CPROVER_assert(bool, const char *);

struct G
{
  int a = 1;
  int b = 2;
  int c = 3;
};

struct H
{
  int a;
  int b;
  int c;
};

struct F
{
  unsigned short a : 1 {false};
  unsigned short b : 1 {false};
  unsigned short c : 3 {false};
  unsigned short d : 2 {false};
};

inline constexpr F gb{.b = true, .d = true};
constexpr F gz{};
constexpr G gg{.c = 9};

static_assert(gb.a == 0 && gb.b == 1 && gb.c == 0 && gb.d == 1, "ns bits");
static_assert(gz.b == 0 && gz.d == 0, "ns empty list");
static_assert(gg.a == 1 && gg.b == 2 && gg.c == 9, "ns designated");

int main()
{
  G g1{.a = 7};
  __CPROVER_assert(g1.a == 7 && g1.b == 2 && g1.c == 3, "first designated");
  G g2{.c = 7};
  __CPROVER_assert(g2.a == 1 && g2.b == 2 && g2.c == 7, "last designated");
  G g3{.a = 8, .c = 9};
  __CPROVER_assert(g3.a == 8 && g3.b == 2 && g3.c == 9, "two designated");
  G g4{5};
  __CPROVER_assert(g4.a == 5 && g4.b == 2 && g4.c == 3, "positional");
  H h{.b = 4};
  __CPROVER_assert(h.a == 0 && h.b == 4 && h.c == 0, "no default member init");

  F f{.c = true};
  __CPROVER_assert(f.a == 0 && f.b == 0 && f.c == 1 && f.d == 0, "bit-fields");
  F p{true};
  __CPROVER_assert(p.a == 1 && p.c == 0, "bit-fields positional");
  __CPROVER_assert(gb.b == 1 && gb.c == 0 && gb.d == 1, "ns bits at run time");

  constexpr F k;
  static_assert(k.a == 0 && k.c == 0, "block-scope constexpr bit-fields");

  __CPROVER_assert(g2.a == 0, "WRONG (must FAIL)");
}

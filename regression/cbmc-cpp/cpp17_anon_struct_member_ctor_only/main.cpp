// Header-free reproducer cvise-reduced from
// cpp17_goto_symex_state_header (CBMC dog-food): a class template
// containing an ANONYMOUS STRUCT whose member has the (ctor-only)
// element type, instantiated via a member alias
// (vector<symbol_exprt>), makes the front end demand a default
// constructor: "found no match for symbol 'symbol_exprt'" with empty
// argument types.  g++/clang++ accept and run clean.
extern "C" void __CPROVER_assert(bool, const char *);

template <typename _Tp> struct vector {
  struct {
    _Tp _M_val;
  };
};
struct nullary_exprt {};
struct symbol_exprt : nullary_exprt {
  symbol_exprt(int) {}
  using variablest = vector<symbol_exprt>;
};

int main() {
  symbol_exprt s(1);
  (void)s;
  __CPROVER_assert(true, "anonymous-struct member of ctor-only type");
  return 0;
}

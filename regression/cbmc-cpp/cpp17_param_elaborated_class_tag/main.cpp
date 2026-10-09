// N5008 [dcl.type.elab], [basic.scope.pdecl]: the elaborated-type-
// specifier `class widget` in a constructor's parameter list
// FIRST-declares widget in the nearest enclosing namespace scope; the
// later member `widget &ref;` may then use the plain name.  CBMC
// registered the tag correctly but processed CONSTRUCTORS in a second
// pass over the class body, so the data member was typechecked before
// the declaration existed ("symbol 'widget' is unknown") -- the shape
// of cpp_typecheck_resolve.h's `class cpp_typecheckt &` parameter,
// which blocked 19 dog-food files.
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct holder
{
  explicit holder(class widget &w) : ref(w)
  {
  }

protected:
  widget
    &ref; // widget was declared by the parameter's elaborated-type-specifier

public:
  widget &get()
  {
    return ref;
  }
};

class widget
{
public:
  int v;
};

int main()
{
  widget w;
  w.v = 6;
  holder h(w);
  __CPROVER_assert(h.get().v == 6, "class declared in parameter usable");
  return 0;
}

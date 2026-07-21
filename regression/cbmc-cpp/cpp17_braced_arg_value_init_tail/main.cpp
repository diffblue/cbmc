// N5008 [dcl.init.aggr]/5 + [over.ics.list]: a braced-init-list
// argument may have FEWER initializers than the aggregate parameter
// has elements; the remaining elements are value-initialized.  CBMC's
// candidate-viability test required an exact element count, and the
// conversion builder gave up when the list ran short -- additionally,
// a compiler-SYNTHESIZED constructor (triggered by any non-POD member,
// here `text`) was mistaken for a user-declared one, disqualifying the
// aggregate entirely ([dcl.init.aggr]/1 only excludes USER-declared
// constructors).  The shape of cpp_scope.h's lookup cache:
//   cache[{this, name}]
// with trailing defaulted key fields.
// g++/clang++ accept and verify at runtime.
extern "C" void __CPROVER_assert(bool, const char *);

struct text
{
private:
  unsigned no;

public:
  unsigned get() const
  {
    return no;
  }
};

struct scopet;

struct keyt
{
  const scopet *scope;
  int kind;
  text name; // non-POD tail: value-initialized when omitted
};

struct tablet
{
  int last_kind;
  unsigned last_no;
  int &operator[](const keyt &k)
  {
    last_kind = k.kind;
    last_no = k.name.get();
    return last_kind;
  }
};

struct scopet
{
  int lookup()
  {
    tablet cache;
    return cache[{this, 3}]; // [dcl.init.aggr]/5: name value-initialized
  }
};

int main()
{
  scopet s;
  __CPROVER_assert(s.lookup() == 3, "given elements stored");
  return 0;
}

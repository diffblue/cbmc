// N5008 [over.match.list], [dcl.init.list]/3, [over.match.best]: a
// braced-init-list argument to a function whose parameter is a class type is
// copy-list-initialized -- the parameter type's constructors are considered
// with the braced-init-list's elements as arguments.  This works for a free
// function but NOT for a member function call: `m.insert({a, b})` fails to
// resolve ("found no match for symbol 'insert'").  g++/clang++ accept it.
//
// This is the root of the dominant "found no match for symbol 'insert'" cluster
// in the src/util/ dog-food (e.g. `parameter_indices.insert({end_id, 0})` on a
// std::unordered_map): the map's value_type (a std::pair) is constructed from
// the braced-init-list.  It is NOT an eager-instantiation problem (found by
// cvise-reducing the noisy preprocessed source).
//
// KNOWN BUG: the member-call overload resolution does not consider the
// braced-init-list -> class-parameter conversion that the free-function path
// already handles.  Flip to CORE once member calls accept braced-init-list
// arguments for class-typed parameters.  assertion.2 must FAIL (non-vacuity).

extern "C" void __CPROVER_assert(int, const char *);

struct pair
{
  int a;
  int b;
  pair(int x, int y) : a(x), b(y) {}
};

struct Map
{
  pair stored{-1, -1};
  void insert(pair p)
  {
    stored = p;
  }
};

int main()
{
  Map m;
  m.insert({5, 9}); // braced-init-list -> pair via pair(int,int), member call
  __CPROVER_assert(
    m.stored.a == 5 && m.stored.b == 9,
    "member insert({a,b}) constructs the class parameter");
  __CPROVER_assert(m.stored.a != 5, "WRONG must FAIL");
  return 0;
}

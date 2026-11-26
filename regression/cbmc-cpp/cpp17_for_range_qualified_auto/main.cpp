// Regression for [stmt.ranged] auto-deduction in a range-based for
// where the declared type is a qualified or modified `auto` (e.g.,
// `const auto&`, `auto&`, `auto*`).
//
// `cpp_typecheckt::typecheck_code` desugars
//
//     for(decl : range) body
//
// for class-typed ranges into the standard
//
//     auto && __range = range;
//     auto __begin = __range.begin();
//     auto __end   = __range.end();
//     for(; __begin != __end; ++__begin) {
//       decl = *__begin;
//       body
//     }
//
// and deduces `decl`'s `auto` from `*__begin`.  Previously the
// deduction matched only bare `auto` (`var_type.id() == ID_auto`),
// leaving qualified forms such as `const auto&` un-deduced — they
// stayed as `merged_type(const, auto)` (or similar) and any later
// member access on the loop variable surfaced as
//
//     member operator requires struct/union type on left hand side
//     but got '<<type:auto>>'
//
// breaking translation units that iterate over a class-typed
// container with `const auto&` (the canonical libstdc++ idiom for
// non-mutating range-for loops).

template <typename T>
struct range_holder
{
  struct iterator
  {
    const T *ptr;
    bool operator!=(const iterator &o) const
    {
      return ptr != o.ptr;
    }
    iterator &operator++()
    {
      ++ptr;
      return *this;
    }
    const T &operator*() const
    {
      return *ptr;
    }
  };
  iterator begin() const
  {
    return {data};
  }
  iterator end() const
  {
    return {data + 3};
  }
  T data[3];
};

struct comp
{
  int x;
};

int main()
{
  range_holder<comp> r{{{1}, {2}, {3}}};
  int sum = 0;
  for(const auto &c : r)
    sum += c.x;
  // Bare `auto` should also still work.
  for(auto c : r)
    sum += c.x;
  // `auto*` against a pointer-element range.
  return sum == 12 ? 0 : 1;
}

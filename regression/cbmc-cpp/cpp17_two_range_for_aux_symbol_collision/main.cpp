// Regression for [stmt.ranged]: each range-based for in the same
// function must use a unique set of auxiliary symbols
// (`__range`/`__begin`/`__end`).  Without a per-loop suffix, the
// second range-for's `symbol_table.insert` of `<scope>::__for_begin`
// (etc.) silently fails because the first range-for already inserted
// a symbol with that name; the second loop then re-uses the FIRST
// loop's iterator type via `lookup_ref(begin_id)`, causing the
// iterator dereference and the loop variable `auto`-deduction to
// bind to the wrong element type.
//
// Concrete symptom on CBMC's own source: `lispirep.cpp::irep2lisp`
// has two sequential range-fors:
//
//   for(const auto &irep : src.get_sub())              // vector<irept>
//   for(const auto &irep_entry : src.get_named_sub())  // map of pairs
//
// The second loop's `auto` was deduced as `irept` (from the first
// loop's `__for_begin`), surfacing as the spurious diagnostic
//
//   symbol 'first' is unknown
//
// when the body referenced `irep_entry.first`.  Three CBMC source
// files (`irep.cpp`, `lispirep.cpp`, `merge_irep.cpp`) hit this
// pattern.
//
// Synthetic container avoids pulling in libstdc++'s forward_list
// internals, keeping the test focused on the typecheck path.

template <typename T>
struct iterator_t
{
  T *p;
  T &operator*() const
  {
    return *p;
  }
  iterator_t &operator++()
  {
    ++p;
    return *this;
  }
  bool operator!=(const iterator_t &other) const
  {
    return p != other.p;
  }
};

template <typename T>
struct list_t
{
  T data[4];
  iterator_t<T> begin()
  {
    return {&data[0]};
  }
  iterator_t<T> end()
  {
    return {&data[0]};
  }
};

struct pair_t
{
  int first;
  int second;
};

struct elem_t
{
  int x;
};

int test()
{
  list_t<elem_t> sub;
  list_t<pair_t> named_sub;
  int count = 0;

  // First range-for: deref → elem_t.
  for(const auto &e : sub)
  {
    count += e.x;
  }

  // Second range-for: deref → pair_t.
  // Pre-fix, this got auto-deduced as `elem_t` (from the first
  // range-for's leaked `__for_begin` aux symbol), surfacing as
  // the spurious diagnostic
  //   symbol 'first' is unknown
  // when the body references `entry.first`.
  for(const auto &entry : named_sub)
  {
    count += entry.first;
  }

  return count;
}

int main()
{
  return test();
}

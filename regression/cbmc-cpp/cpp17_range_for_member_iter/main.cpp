// Regression test for N5008 [stmt.ranged]/1.3.2: range-based `for`
// over a class type with member `begin()`/`end()` iterators.
//
// Pre-fix, CBMC's `for_range` lowering in cpp_typecheck_code.cpp
// only handled the [stmt.ranged]/1.3.1 array path and emitted
// "range-based for requires an array type" for any class-typed
// range expression.  The fix adds the [stmt.ranged]/1.3.2
// desugaring:
//
//   {
//     auto && __range = range-init;
//     auto __begin = __range.begin();
//     auto __end   = __range.end();
//     for (; __begin != __end; ++__begin) {
//       for-range-decl = *__begin;
//       statement
//     }
//   }
//
// with operator overload resolution handling `*`, `++`, and `!=`.

struct iter_t
{
  int *p;
  int operator*() const
  {
    return *p;
  }
  iter_t &operator++()
  {
    ++p;
    return *this;
  }
  bool operator!=(const iter_t &o) const
  {
    return p != o.p;
  }
};

struct my_range
{
  int *data;
  int *data_end;
  iter_t begin()
  {
    return iter_t{data};
  }
  iter_t end()
  {
    return iter_t{data_end};
  }
};

int main()
{
  int arr[5];
  arr[0] = 1;
  arr[1] = 2;
  arr[2] = 3;
  arr[3] = 4;
  arr[4] = 5;

  my_range r{arr, arr + 5};
  int sum = 0;
  for(int x : r)
    sum += x;

  __CPROVER_assert(sum == 15, "sum is 15");
  return 0;
}

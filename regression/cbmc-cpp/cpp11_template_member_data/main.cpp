// Closer reproducer of MSVC atomic_flag::_Storage pattern.
// Key ingredients captured:
//   * Primary template declared with default arg that uses sizeof(T).
//   * Body provided only via partial specializations (_Atomic_storage
//     on N=1,2,4,8).
//   * Intermediate layer inherits the primary (no size arg) so the
//     specialization selection happens at the leaf.
//   * Outer struct has a data member of the outer class template
//     declared AFTER the methods that use it.

// primary: just a forward declaration with a sizeof(T) default
template <class T, unsigned N = sizeof(T)>
struct Storage;

// partial specialization for N=8 (covers long on LP64)
template <class T>
struct Storage<T, 8>
{
  T val;
  T exchange(T v)
  {
    T old = val;
    val = v;
    return old;
  }
};

// intermediate: inherits primary, selecting partial spec
template <class T>
struct Integral : Storage<T>
{
};

// atomic<T>: inherits intermediate
template <class T>
struct Atomic : Integral<T>
{
};

// outer class with methods using member before it's declared, and
// the member's type is the outer class template specialization
struct Flag
{
  long test_and_set(long v)
  {
    return storage.exchange(v);
  }
  Atomic<long> storage;
};

int main()
{
  Flag f;
  f.storage.val = 0;
  long prev = f.test_and_set(7);
  __CPROVER_assert(prev == 0, "deep-template member exchange prev");
  __CPROVER_assert(f.storage.val == 7, "deep-template member exchange new");
  return 0;
}

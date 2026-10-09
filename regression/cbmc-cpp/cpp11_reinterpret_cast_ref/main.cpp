// Per [expr.reinterpret.cast]/11: a glvalue of type T1 can be cast
// to reference type T2& when a pointer to T1 can be converted to a
// pointer to T2; the resulting glvalue refers to the same storage.
//
// Per [expr.unary.op]/3: if the operand of & is a reference, the
// result is the address of the referred-to object.
//
// MSVC's <atomic> uses this pattern for its spinlock implementation:
//   inline void _Atomic_lock_acquire(long& _Spinlock) noexcept {
//     while (_InterlockedExchange(&_Spinlock, 1) != 0) {
//       while (__iso_volatile_load32(
//                &reinterpret_cast<int&>(_Spinlock)) != 0)
//         ...
//     }
//   }
//
// Before the fix:
//   * cpp_typecheck_conversions.cpp's reinterpret_cast-to-reference
//     path produced a typecast-of-address-of that did not carry the
//     reference flag cleanly;
//   * cpp_typecheck_expr.cpp's typecheck_expr_address_of did not
//     implicitly dereference a reference operand.
// Together these meant that `&reinterpret_cast<int&>(x)` failed with
//   "address_of error: '&(*x)' not an lvalue"
// at type-check time.

void use_int_ptr(int *);

void call_it(long &x)
{
  use_int_ptr(&reinterpret_cast<int &>(x));
}

int read_through_ref(long &x)
{
  int &r = reinterpret_cast<int &>(x);
  return r;
}

int direct_return(long &x)
{
  return reinterpret_cast<int &>(x);
}

int main()
{
  long l = 42;
  __CPROVER_assert(read_through_ref(l) == 42, "reinterpret_cast to reference");
  __CPROVER_assert(direct_return(l) == 42, "reinterpret_cast direct return");
  return 0;
}

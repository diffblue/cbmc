int main()
{
  __CPROVER_integer arr[3];
  __CPROVER_integer i;
  // i is fully unconstrained: it may be negative (lower-bound violation) or
  // >= 3 (upper-bound violation), so both generated checks must be able to
  // fail.  This confirms the checks are meaningful, not vacuously true.
  __CPROVER_integer x = arr[i];
  __CPROVER_assert(1, "reachable");
}

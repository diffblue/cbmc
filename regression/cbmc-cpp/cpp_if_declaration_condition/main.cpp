// C++ [stmt.select]/1-2, [stmt.if]: an if-statement condition may be a
// declaration; the value tested is the declared variable contextually
// converted to bool, and the variable is in scope in both substatements.
//
// Regression: the C++ frontend type-checked such a declaration but left the
// condition as the declaration code itself, so the "then" branch was never
// taken (the condition behaved as if always false).  This silently broke,
// among other things, libstdc++ vector::_M_erase_at_end's
// `if (size_type __n = _M_finish - __pos)`, used by clear()/resize()/
// erase(first, last).  Header-free coverage of the fix.

int side_effect_calls = 0;
int make(int v)
{
  ++side_effect_calls;
  return v;
}

int main()
{
  // Non-zero initializer: branch taken, variable visible in the branch.
  int taken = 0;
  if(int x = 3)
    taken = x;
  __CPROVER_assert(taken == 3, "if(int x=3): branch taken, x==3");

  // Zero initializer: branch not taken; else branch sees the variable.
  int via_else = 0;
  if(int y = 0)
    via_else = -1;
  else
    via_else = y + 7;
  __CPROVER_assert(via_else == 7, "if(int y=0): else taken, y==0");

  // Pointer declaration condition (the classic `if(void *p = ...)`).
  int storage = 42;
  if(int *p = &storage)
    __CPROVER_assert(*p == 42, "if(int *p=&storage): p non-null, *p==42");
  else
    __CPROVER_assert(0, "unreachable: &storage is never null");

  // The condition's initializer is evaluated exactly once.
  if(int z = make(5))
    __CPROVER_assert(z == 5, "if(int z=make(5)): z==5");
  __CPROVER_assert(side_effect_calls == 1, "condition initializer runs once");

  return 0;
}

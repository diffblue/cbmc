int main()
{
  int a = 10;

  // gcc: error: redeclaration of 'a' with no linkage.
  // The second declaration carries an initializer; it must still be rejected
  // (it was wrongly accepted while the __auto_type double-typecheck was worked
  // around in typecheck_symbol, silently dropping the second initializer).
  int a = 20;

  return a;
}

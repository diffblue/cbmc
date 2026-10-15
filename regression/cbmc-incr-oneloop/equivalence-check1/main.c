extern int nondet_int();
int main()
{
  int x = nondet_int();
  __CPROVER_assume(0 <= x && x <= 8);
  int sum = 0;
  int count = 0;
  while(x > 0)
  {
    sum = sum + x;
    count = count + 1;
    x = x - 1;
    assert(count >= 1);   // always true
    assert(sum >= count); // always true
    assert(x >= 0);       // always true
  }
  assert(count <= 8); // always true
  assert(sum <= 36);  // always true (max: 8+7+...+1 = 36)
  assert(sum <= 10);  // FAILS for x >= 5
  assert(x == 0);     // always true
}

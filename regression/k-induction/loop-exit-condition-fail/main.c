// Polarity guard (failing variant). After the loop i is 2, so i < 2 is false
// and must be reported as a violation. This is exactly the case an inverted
// loop-exit assume would mask: assuming the *continue* condition (i < 2)
// prunes the true exit state (i == 2), spuriously "verifying" the property.
int main()
{
  unsigned i = 0;
  while(i < 2)
    i++;
  __CPROVER_assert(i < 2, "i < 2 must fail at loop exit");
}

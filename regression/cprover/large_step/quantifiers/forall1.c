int main()
{
  __CPROVER_assert(∀ int i; i == 100, "all ints are 100"); // fails
  __CPROVER_assert(∀ int i; 1, "true holds for all i");    // passes
  __CPROVER_assert(∀ unsigned char ch;
                   ch <= 255, "all chars are ≤255"); // passes
  return 0;
}

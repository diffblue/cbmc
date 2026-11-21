int main()
{
  __CPROVER_assert(∃ int i; i == 100, "100 exists");      // passes
  __CPROVER_assert(∃ int i; 0, "'false' does not exist"); // fails
}

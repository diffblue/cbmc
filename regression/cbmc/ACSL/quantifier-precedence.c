int main()
{
  // ∀ binds very weakly.
  // In particular, 'i' below is in the scope of the quantifier.
  __CPROVER_assert(∀ int i; 1 ? 1 : i, "∀ binds weakly");
}

void boolean()
{
  __CPROVER_bool a, b;
  __CPROVER_assert((a ≡ b) == (a == b), "≥");
  __CPROVER_assert((a ≢ b) == (a != b), "≢");
  __CPROVER_assert((a ⇒ b) == (!a || b), "⇒");
  __CPROVER_assert((a ⇔ b) == (a == b), "⇔");
  __CPROVER_assert((a ∧ b) == (a && b), "∧");
  __CPROVER_assert((a ∨ b) == (a || b), "∨");
  __CPROVER_assert((a ⊻ b) == (a != b), "⊻");
  __CPROVER_assert((¬ a) == (!a), "¬");
}

void relations()
{
  int a, b;
  __CPROVER_assert((a ≥ b) == (a >= b), "≥");
  __CPROVER_assert((a ≤ b) == (a <= b), "≤");
  __CPROVER_assert((a ≡ b) == (a == b), "≥");
  __CPROVER_assert((a ≢ b) == (a != b), "≢");
  __CPROVER_assert((− a) == (-a), "−");
}

int main()
{
  boolean();
  relations();
}

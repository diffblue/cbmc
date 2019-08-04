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

void quantifiers()
{
  __CPROVER_assert((∀ int i; 1) == 1, "∀");
  __CPROVER_assert((∃ int i; 1) == 1, "∃");
}

int main()
{
  boolean();
  relations();
  quantifiers();
}

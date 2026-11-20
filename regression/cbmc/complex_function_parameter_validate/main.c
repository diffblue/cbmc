// A function taking and returning a complex number: remove_complex lowers
// the parameter symbols to { real, imag } structs, and must lower the
// function's type with them, or --validate-goto-model reports a "parameter
// type inconsistency".
_Complex float swap(_Complex float z)
{
  return __imag__ z + 1.0if * __real__ z;
}

int main()
{
  _Complex float z = 1.0f + 2.0if;
  _Complex float (*fp)(_Complex float) = swap;
  _Complex float w = fp(z);
  __CPROVER_assert(__real__ w == 2.0f && __imag__ w == 1.0f, "swapped");
  return 0;
}

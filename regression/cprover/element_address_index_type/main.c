int a[10];

int main()
{
  int i, j;

  // Two element_address expressions that share a result (pointer) type. The
  // SMT2 helper function emitted for ID_element_address is named after both
  // the result type and the index type, so the index type must appear in the
  // declare-fun name. This guards the disambiguation: without it the name
  // would be keyed on the result type alone, and two such expressions with
  // differing index sorts would reuse one name with mismatched argument
  // sorts, which a solver rejects.
  int x = a[i];
  int y = a[j];

  __CPROVER_assert(x == y, "x equals y");

  return 0;
}

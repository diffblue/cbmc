// In order to ensure that the stub is correctly generated, the
// contract should make the harness succeed while the function body
// should make it fail.
int stub() __CPROVER_ensures(__CPROVER_return_value == 42)
{
  return 0;
}

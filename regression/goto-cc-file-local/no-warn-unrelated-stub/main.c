// ext_only is a genuinely external, bodiless function with no file-local twin.
// Even though the program has a file-local body (local_helper in impl.c), the
// bodiless call to ext_only must NOT trigger the file-local-stub warning, because the
// warning is specific to file-local-shadowed symbols.
extern int ext_only(int);
int harness(void)
{
  return ext_only(0);
}
int main(void)
{
  return harness();
}

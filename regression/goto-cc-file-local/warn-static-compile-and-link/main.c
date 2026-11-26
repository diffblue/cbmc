// The harness calls _recv via an `extern` (unmangled) declaration.  _recv is
// actually `static` in impl.c, so with --export-file-local-symbols it is
// mangled to __CPROVER_file_local_impl_c__recv and does NOT satisfy the
// extern call.  At link time _recv therefore has no body, and goto-cc warns
// about this.
extern int _recv(int);
int harness(void)
{
  return _recv(0);
}
int main(void)
{
  return harness();
}

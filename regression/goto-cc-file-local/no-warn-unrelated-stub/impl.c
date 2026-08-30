// local_helper is `static`, so with --export-file-local-symbols it is mangled
// to __CPROVER_file_local_impl_c_local_helper (with a body).  This makes the
// stub scan run, but the only bodiless call below is to an unrelated
// external `ext_only`, which has no file-local twin -- so no warning must be
// emitted.  (Ordinary bodiless library symbols behave the same way.)
static int local_helper(int x)
{
  return x + 1;
}
int kernel_entry(void)
{
  return local_helper(7);
}

// The ERROR label lives in unreachable(), which is never called from main().
// --error-label turns such labels into assertions inside goto_check_c, but
// that runs after --drop-unused-functions has removed the function, so the
// error-label assertion is elided together with the dropped function.
void unreachable(void)
{
ERROR:
  return;
}

int main(void)
{
  return 0;
}

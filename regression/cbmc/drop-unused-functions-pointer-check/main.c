// unreachable() is never called from main(), so --drop-unused-functions
// removes it before property instrumentation. Its null dereference must
// therefore never be turned into a property.
void unreachable(void)
{
  int *p = 0;
  *p = 0;
}

int main(void)
{
  return 0;
}

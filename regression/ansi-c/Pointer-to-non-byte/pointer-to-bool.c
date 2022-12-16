__CPROVER_bool x;

int main()
{
  void *p = &x; // should error
}

const int months = 12;

int main()
{
  char *p;
  __CPROVER_assume(__CPROVER_WRITEABLE_OBJECT(p));
  __CPROVER_assert(!__CPROVER_same_object(p, &months), "property 1"); // passes
}

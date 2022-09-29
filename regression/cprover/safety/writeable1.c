const int months = 12;
int x;

void *malloc(__CPROVER_size_t);

int main()
{
  __CPROVER_assert(__CPROVER_WRITEABLE_OBJECT(&x), "property 1");       // holds
  __CPROVER_assert(!__CPROVER_WRITEABLE_OBJECT(&months), "property 2"); // holds
  __CPROVER_assert(
    !__CPROVER_WRITEABLE_OBJECT("foobar"), "property 3"); // holds
  __CPROVER_assert(
    __CPROVER_WRITEABLE_OBJECT(malloc(1)), "property 1"); // holds
}

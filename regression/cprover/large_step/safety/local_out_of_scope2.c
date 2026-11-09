int main()
{
  void *p;
  __CPROVER_assume(__CPROVER_LIVE_OBJECT(p));

  {
    void *q; // unrelated to p
  }

  __CPROVER_assert(__CPROVER_LIVE_OBJECT(p), "property 1"); // passes
}

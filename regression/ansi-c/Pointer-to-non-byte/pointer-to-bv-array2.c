__CPROVER_bitvector[123] z[10];

int main()
{
  void *p = (int *)z; // should error
}

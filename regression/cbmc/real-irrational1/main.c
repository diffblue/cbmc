int main()
{
  __CPROVER_real a;
  __CPROVER_real a2 = a * a;
  __CPROVER_assert(a2 != 2, "");
}

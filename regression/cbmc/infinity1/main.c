int A[__CPROVER_constant_infinity_uint];

int main()
{
  __CPROVER_assert(__CPROVER_OBJECT_SIZE(A) > 0, "infinity is positive");
}

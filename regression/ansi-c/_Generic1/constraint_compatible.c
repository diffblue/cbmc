int main(void)
{
  // C11 6.5.1.1p2: no two generic associations shall specify compatible
  // types, even if neither matches the controlling expression.
  return _Generic(1.0, int(*)[]: 1, int(*)[5]: 2, default: 3);
}

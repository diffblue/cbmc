int main(void)
{
  // C11 6.5.1.1p2: at most one default generic association
  return _Generic(0, default: 1, default: 2);
}

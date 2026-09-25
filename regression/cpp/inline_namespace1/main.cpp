namespace outer
{
inline namespace inner
{
struct S
{
  int x;
};
} // namespace inner
// S should be visible here via inline namespace
S make()
{
  S s;
  s.x = 42;
  return s;
}
} // namespace outer

int main()
{
  outer::S s1 = outer::make();
  outer::inner::S s2 = s1;
  return 0;
}

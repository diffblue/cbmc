// C++11 noexcept operator
void may_throw();
void no_throw() noexcept;
int main()
{
  __CPROVER_assert(!noexcept(may_throw()), "may_throw is not noexcept");
  __CPROVER_assert(noexcept(no_throw()), "no_throw is noexcept");
  return 0;
}

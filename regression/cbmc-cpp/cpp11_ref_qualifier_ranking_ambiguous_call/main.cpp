// N5008 [over.match.best.general]/2, [over.ics.rank]/3.2.3, /3.2.6: for
// `S().f(x)', f() && binds the rvalue object better (3.2.3) and
// f(int &) binds x better (3.2.6, less cv-qualified); neither candidate is
// better for every argument, so the call is ambiguous and the program is
// ill-formed.  CBMC ranks 3.2.3 as a cv tie-breaker summed over the
// arguments (fargs.match's cv_distance) and silently picks one.
struct S
{
  int f(int &) const &
  {
    return 1;
  }
  int f(const int &) &&
  {
    return 2;
  }
};
int main()
{
  int x = 0;
  return S().f(x);
}

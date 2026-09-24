// Calling a function without a body produces a "no body for callee" assertion
// that is generated during symbolic execution rather than collected from the
// goto program up front. With no other (statically known) property present,
// the single-path checker's has_finished_exploration would report completion
// before exploring any path unless paths-symex-explore-all is set, so under
// --paths lifo this property must still be reported as failing.
void no_body(void);

int main()
{
  no_body();
  return 0;
}

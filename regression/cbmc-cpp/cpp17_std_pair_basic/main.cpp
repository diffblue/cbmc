// Regression for the std::pair member-function-template signature
// typecheck during class body elaboration.
//
// libstdc++'s `std::pair<_T1, _T2>` defines several constructor
// templates whose signatures reference the function template's own
// parameters (e.g. `pair(const pair<_U1, _U2>& __p)` where _U1 and
// _U2 belong to the constructor template, not to the enclosing
// class).  Before the fix, the second pass of
// `typecheck_compound_body` called `typecheck_compound_declarator`
// on these constructor templates without populating the
// `template_map` with the function template's own parameters.
// `convert_template_parameter`'s lookup of `_U1` then fell through
// to a silent `throw 0`, which propagated out of
// `instantiate_template` and was caught by the enclosing
// `typecheck_method_bodies` as a template-instantiation failure.
// The user's `main` body was left half-typechecked, the
// `std::pair<int, int> p;` declaration was silently dropped, and
// only the `tag-std::pair<int,int>` shell remained — and even that
// got removed by `linking/remove_internal_symbols` because nothing
// referenced it.
//
// After the fix, the second-pass loop populates `template_map`
// with `unassigned`-typed placeholders for the constructor
// template's TYPE parameters, so `convert_template_parameter`
// returns the placeholder rather than throwing.  The constructor
// template's signature typechecks (with abstract parameter types),
// the class instantiation completes, and the user's `p` survives
// into the goto model.

#include <utility>

int main()
{
  std::pair<int, int> p;
  return 0;
}

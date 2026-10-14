// N5008 [basic.lookup.argdep]/1.3: when unqualified lookup of the called
// name finds a declaration that is not of a function or function template,
// argument-dependent lookup is not performed.  The block-scope object
// `analysis' hides an::analysis, and `analysis(m)' calls its operator().
// The front end also collected an::analysis by ADL (m is an an::model):
// "symbol 'analysis' does not uniquely resolve" (CBMC's own
// goto_instrument_parse_options.cpp, `ait<interval_domaint>
// interval_analysis; interval_analysis(goto_model);', dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
namespace an
{
struct model
{
  int n = 4;
};
int analysis(model &m)
{
  return m.n;
}
} // namespace an
using an::analysis;
struct ai
{
  int seen = 0;
  void operator()(an::model &m)
  {
    seen = m.n + 1;
  }
};
int main()
{
  an::model m;
  // N5008 [basic.lookup.unqual]: the block-scope variable hides
  // an::analysis; [basic.lookup.argdep]/3.2: lookup finds an object, so
  // argument-dependent lookup is not performed and this calls operator()
  ai analysis;
  analysis(m);
  __CPROVER_assert(analysis.seen == 5, "the variable's operator() called");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

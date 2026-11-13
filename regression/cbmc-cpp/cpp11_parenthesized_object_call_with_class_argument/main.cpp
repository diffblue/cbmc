// N5008 [expr.cast]/2, [expr.call]/1: `(shared)(k)' is a cast only if
// `shared' names a type.  It names an object here, so the expression calls
// operator() of its class.  With a class-type operand the front end first
// looked for a conversion function to the "type" `shared' and failed:
// "found no match for symbol 'shared'" (CBMC's own shared_buffers.cpp,
// `(shared_buffers)(r_entry.second.object)', dog-fooding).
extern "C" void __CPROVER_assert(bool, const char *);
struct id_t
{
  int n;
};
class bufs
{
public:
  int base = 10;
  int operator()(const id_t &k)
  {
    return base + k.n;
  }
  class visitor
  {
  public:
    bufs &shared;
    explicit visitor(bufs &b) : shared(b)
    {
    }
    int get(const id_t &k);
  };
};
int bufs::visitor::get(const id_t &k)
{
  // N5008 [expr.cast]/2, [expr.call]: `shared' names an object, so this
  // is a call of its operator(), not a cast
  const int &r = (shared)(k);
  return r;
}
int main()
{
  bufs b;
  bufs::visitor v{b};
  __CPROVER_assert(v.get(id_t{2}) == 12, "parenthesized object called");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

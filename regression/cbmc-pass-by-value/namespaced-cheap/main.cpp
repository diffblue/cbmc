struct dstringt
{
  unsigned n;
};

namespace other_ns
{
struct dstringt
{
  unsigned n;
};
} // namespace other_ns

// Only the global ::dstringt is cheap; other_ns::dstringt must NOT match,
// even though its simple name is also "dstringt".
void f(const other_ns::dstringt &x);

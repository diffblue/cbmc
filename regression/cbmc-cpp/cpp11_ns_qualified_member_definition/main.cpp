// N5008 [class.mfct]/1 + [namespace.qual]: an out-of-line member
// definition may carry a redundant namespace qualifier even inside
// that namespace (libstdc++ <streambuf>'s defaulted
// basic_streambuf copy constructor).  The A::B<args>::member handler
// only tried the leading component as a CLASS; the namespace form
// failed the whole translation unit ("class template 'std' not
// found").  252-byte cvise harvest (cx2, second layer) of the
// preprocessed libstdc++ <regex> seed.
extern "C" void __CPROVER_assert(bool, const char *);
namespace std
{
template <typename> struct basic_streambuf
{
  basic_streambuf(const basic_streambuf &);
};
template <typename _Traits>
std::basic_streambuf<_Traits>::basic_streambuf(const basic_streambuf &) =
  default;
} // namespace std
int main()
{
  __CPROVER_assert(true, "converts");
  return 0;
}

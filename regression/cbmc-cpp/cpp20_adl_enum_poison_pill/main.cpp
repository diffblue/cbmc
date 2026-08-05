// N5008 [basic.lookup.argdep]/2.3: the associated entities of an
// ENUMERATION type include its innermost enclosing namespace.  CBMC's
// ADL only associated CLASS types, so libc++'s poison-pill pattern --
//   using __adl_only::make_error_code;      // deleted
//   *this = make_error_code(__e);           // real overload via ADL
// (std::error_code's converting constructor over io_errc/future_errc)
// found only the deleted pill and the whole <system_error> chain
// failed "found no match for symbol 'make_error_code'".
extern "C" void __CPROVER_assert(bool, const char *);
namespace std {
namespace __adl_only {
void make_error_code() = delete;
}
struct error_code {
  int v;
  template <class E> error_code(E e) {
    using __adl_only::make_error_code;
    *this = make_error_code(e);
  }
  error_code(int val, bool) : v(val) {}
};
}
enum class io_errc { stream = 1 };
std::error_code make_error_code(io_errc e) {
  return std::error_code(static_cast<int>(e), true);
}
int main() {
  std::error_code ec(io_errc::stream);
  __CPROVER_assert(ec.v == 1, "adl make_error_code");
  return 0;
}

// N5008 [meta.trans.sign], Table 59: make_signed<T> is T for a signed
// integer type, the corresponding signed integer type ([basic.fundamental]
// /2-3, same rank) for an unsigned one, and otherwise the signed integer
// type of the smallest rank with the same size; cv-qualifiers are kept.
// Clang's __make_signed / __make_unsigned (libc++'s make_signed_t) returned
// a bare bit-vector type, not the C type: `type_identity<__make_signed(S)>'
// named a different specialization, and in libc++'s iota_view the
// iterator's constructor then found no viable std::move and lost its body.
extern "C" void __CPROVER_assert(bool, const char *);

template <class T>
struct type_identity
{
  typedef T type;
};
template <class T>
using type_identity_t = typename type_identity<T>::type;

template <class T>
T &&move(T &t)
{
  return static_cast<T &&>(t);
}

static_assert(__is_same(__make_signed(unsigned), int), "unsigned int");
static_assert(__is_same(__make_signed(long), long), "long kept");
static_assert(__is_same(__make_signed(char), signed char), "char");
static_assert(__is_same(__make_unsigned(int), unsigned), "int");
static_assert(
  __is_same(__make_unsigned(unsigned long long), unsigned long long),
  "unsigned long long kept");
static_assert(__is_same(__make_unsigned(char16_t), unsigned short), "char16_t");
static_assert(__is_same(__make_signed(const unsigned), const int), "cv");

template <class S, class B>
struct iota_view
{
  struct iterator
  {
    using difference_type = type_identity_t<__make_signed(S)>;
    S value_;
    iterator(S value) : value_(move(value))
    {
    }
  } bound_;
  iota_view(S, type_identity_t<B> bound) : bound_(move(bound))
  {
  }
};

int main()
{
  iota_view<int, int> v(1, 4);
  __CPROVER_assert(v.bound_.value_ == 4, "iterator constructor");
  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}

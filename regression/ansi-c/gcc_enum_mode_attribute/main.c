// gcc allows __attribute__((mode(...))) on enums (clang doesn't).  A mode name
// may be spelled with or without a surrounding pair of underscores, so "byte"
// is the same as "__byte__".  For a mode we don't recognise at all we fall
// back to the enum's underlying bitvector -- crucially NOT the c_enum_tag,
// which used to make the enum's underlying type its own tag (a cycle) and
// crashed pointer_offset_bits / alignment.  Seen in kernel/crypto headers
// (net/rxrpc, crypto/krb5).

#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef __GNUC__

// special-cased, underscored spelling -> 8 bits
enum E
{
  A,
  B,
  C
} __attribute__((mode(__QI__)));
STATIC_ASSERT(sizeof(enum E) == 1);

// un-underscored spelling of the same mode -> also 8 bits, matching gcc
// (this is the genuinely new coverage; __QI__ above is already in
// gcc_attributes6)
enum F
{
  X,
  Y
} __attribute__((mode(byte)));
STATIC_ASSERT(sizeof(enum F) == 1);

// a mode we do not special-case at all: must fall back without crashing the
// layout computation below.  The width is best-effort -- real gcc would use
// 32 bytes for OI, whereas CBMC keeps the enum's natural underlying width.
enum G
{
  P,
  Q
} __attribute__((mode(OI)));
STATIC_ASSERT(sizeof(enum G) == sizeof(int));

// force layout/alignment computation across all three enums -- this is the
// path that used to crash on the self-referential fallback type
struct s
{
  enum E e;
  enum F f;
  enum G g;
  int tail;
};
STATIC_ASSERT(sizeof(struct s) >= sizeof(int));

#endif

int main()
{
}

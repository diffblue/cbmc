#ifdef __GNUC__

enum { E01 = __builtin_isinf(1.0) };
enum { E02 = __builtin_isnan(1.0) };
enum { E03 = __builtin_isinf(__builtin_inf()) };
enum { E04 = __builtin_signbit(-1.0) }; // clang doesn't do this one
enum { E05 = __builtin_classify_type(1) };
enum { E06 = sizeof(int) };
enum { E07 = __alignof__(int) };
enum { E08 = (int)1.0 };
enum { E09 = __builtin_popcount(123) };
enum { E10 = __builtin_bswap16(0xaabb) };
enum { E11 = __builtin_bswap32(0xaabb) };
enum { E12 = __builtin_bswap64(0xaabb) };

#endif

int main()
{
}

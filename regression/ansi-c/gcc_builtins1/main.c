#ifdef __GNUC__

enum { E1 = __builtin_isinf(1.0) };
enum { E2 = __builtin_isnan(1.0) };
enum { E3 = __builtin_isinf(__builtin_inf()) };
enum { E4 = __builtin_signbit(-1.0) };
enum { E5 = __builtin_classify_type(1) };
enum { E6 = sizeof(int) };
enum { E7 = __alignof__(int) };
enum { E8 = (int)1.0 };

#endif

int main()
{
}

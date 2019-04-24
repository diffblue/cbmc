#ifdef __GNUC__

#  define CONCAT(a, b) a##b
#  define CONCAT2(a, b) CONCAT(a, b)

#  define STATIC_ASSERT(condition)                                             \
    int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// Debian package linux-tools
enum help_format {
  HELP_FORMAT_NONE,
  HELP_FORMAT_MAN,
  HELP_FORMAT_INFO,
  HELP_FORMAT_WEB,
};

// The enums are 'unsigned int'
enum help_format help_format = HELP_FORMAT_MAN;
STATIC_ASSERT(__builtin_types_compatible_p(typeof(&help_format), unsigned int*));

// Ha! The constants themselves are 'signed int'
STATIC_ASSERT(__builtin_types_compatible_p(typeof(HELP_FORMAT_WEB), signed int));
STATIC_ASSERT(!__builtin_types_compatible_p(typeof(HELP_FORMAT_WEB), unsigned int));

enum help_format_neg {
  N_HELP_FORMAT_NONE,
  N_HELP_FORMAT_MAN=-1,
  N_HELP_FORMAT_INFO,
  N_HELP_FORMAT_WEB,
};

// The enum is signed if one of the values is negative
enum help_format_neg help_format_neg = N_HELP_FORMAT_NONE;
STATIC_ASSERT(__builtin_types_compatible_p(typeof(&help_format_neg), int*));

// The underlying type gets unsigned as needed.
enum unsigned_enum { UINT=0xffffffff };
STATIC_ASSERT(__builtin_types_compatible_p(typeof(UINT), unsigned int));
STATIC_ASSERT(__builtin_types_compatible_p(typeof(enum unsigned_enum), unsigned int));

// The enum gets bigger as required, but note that the constant is now unsigned.
enum large_enum1 { LARGE_CONSTANT1=0x100000000 };
STATIC_ASSERT(__builtin_types_compatible_p(typeof(LARGE_CONSTANT1), unsigned long) ||
              __builtin_types_compatible_p(typeof(LARGE_CONSTANT1), unsigned long long));
STATIC_ASSERT(__builtin_types_compatible_p(typeof(enum large_enum1), unsigned long) ||
              __builtin_types_compatible_p(typeof(enum large_enum1), unsigned long long));

// Also works when signed
enum large_enum2 { NEG=-1, LARGE_CONSTANT2=0x100000000 };
STATIC_ASSERT(__builtin_types_compatible_p(typeof(LARGE_CONSTANT2), signed long) ||
              __builtin_types_compatible_p(typeof(LARGE_CONSTANT2), signed long long));
STATIC_ASSERT(__builtin_types_compatible_p(typeof(enum large_enum2), signed long) ||
              __builtin_types_compatible_p(typeof(enum large_enum2), signed long long));

// 'Packed' is interesting.
enum __attribute__((packed)) packed_enum1 { POS_PACKED=1 };
STATIC_ASSERT(__builtin_types_compatible_p(typeof(POS_PACKED), signed int));
STATIC_ASSERT(__builtin_types_compatible_p(typeof(enum packed_enum1), unsigned char));

enum __attribute__((packed)) packed_enum2 { NEG_PACKED=-1 };
STATIC_ASSERT(__builtin_types_compatible_p(typeof(NEG_PACKED), signed int));
STATIC_ASSERT(__builtin_types_compatible_p(typeof(enum packed_enum2), signed char));

#endif

int main()
{
  return 0;
}

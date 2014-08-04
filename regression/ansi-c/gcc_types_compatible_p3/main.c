#ifdef __GNUC__

#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

// Debian package linux-tools
enum help_format {
  HELP_FORMAT_NONE,
  HELP_FORMAT_MAN,
  HELP_FORMAT_INFO,
  HELP_FORMAT_WEB,
};

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

enum help_format_neg help_format_neg = N_HELP_FORMAT_NONE;
STATIC_ASSERT(__builtin_types_compatible_p(typeof(&help_format_neg), int*));

#endif

int main()
{
  return 0;
}

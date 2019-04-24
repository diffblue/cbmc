#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

typedef struct struct_tag
{
  int x;
  float y;
} struct_typedef;

typedef struct struct_tag alt_typedef;
typedef struct_typedef another_typedef;

#ifdef __GNUC__


STATIC_ASSERT(__builtin_types_compatible_p(struct struct_tag, struct_typedef));
STATIC_ASSERT(__builtin_types_compatible_p(struct struct_tag, alt_typedef));
STATIC_ASSERT(__builtin_types_compatible_p(struct struct_tag, another_typedef));
STATIC_ASSERT(__builtin_types_compatible_p(struct_typedef, alt_typedef));
STATIC_ASSERT(__builtin_types_compatible_p(struct_typedef, another_typedef));
STATIC_ASSERT(__builtin_types_compatible_p(alt_typedef, another_typedef));

#endif

int main(void)
{
}

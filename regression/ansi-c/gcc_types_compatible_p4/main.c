#define STATIC_ASSERT(condition) \
  int some_array[(condition) ? 1 : -1];

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

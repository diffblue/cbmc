// asm goto in a file-local (static) function, as in the Linux kernel's
// arch_static_branch (static keys). goto-cc --export-file-local-symbols
// renames the symbols of such functions, which must include the variable that
// selects the label the asm goto jumps to.
struct static_key
{
  int enabled;
};

#ifdef __GNUC__
#  define ALWAYS_INLINE __attribute__((always_inline))
#else
#  define ALWAYS_INLINE
#endif

static inline ALWAYS_INLINE _Bool
arch_static_branch(struct static_key *const key, const _Bool branch)
{
#ifdef __GNUC__
  asm goto(
    "1: jmp %l[l_yes]\n\t"
    ".pushsection __jump_table, \"aw\"\n\t"
    ".long 1b - . \n\t"
    ".popsection\n\t"
    :
    : "i"(key), "i"(branch)
    :
    : l_yes);
  return 0;
l_yes:
  return 1;
#else
  return branch;
#endif
}

struct static_key kc;

int main(void)
{
  int x = arch_static_branch(&kc, 1) ? 1 : 0;
  __CPROVER_assert(x <= 1, "x");
  return 0;
}

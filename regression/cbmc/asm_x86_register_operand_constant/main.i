// A 32-bit input operand whose value is a known constant stays a constant in
// the register that holds it (the upper bits of the register are zero, as no
// reference reads them). Merging the value into a register with
// nondeterministic upper bits would make the lock word written by xchg
// symbolic, so that both spin loops would unwind to the unwinding bound.
typedef int word_t;
typedef struct
{
  word_t locked;
} spin_t;

static inline void spin_lock(spin_t *sl)
{
  word_t lock_val = 1;
  asm volatile(
    "1:\n"
    "xchg %[locked], %[lv]\n"
    "test %[lv], %[lv]\n"
    "jz 3f\n"
    "2:\n"
    "pause\n"
    "cmpl $0, %[locked]\n"
    "jnz 2b\n"
    "jmp 1b\n"
    "3:\n"
    : [locked] "=m"(sl->locked), [lv] "=q"(lock_val)
    : "[lv]"(lock_val)
    : "memory");
}

static inline void spin_unlock(spin_t *sl)
{
  word_t v = 0;
  asm volatile("xchg %[locked], %[ulv]\n"
               : [locked] "=m"(sl->locked), [ulv] "=q"(v)
               : "[ulv]"(v)
               : "memory");
}

int main(void)
{
  spin_t s;
  s.locked = 0;
  for(int i = 0; i < 4; i++)
  {
    spin_lock(&s);
    spin_unlock(&s);
  }
  return 0;
}

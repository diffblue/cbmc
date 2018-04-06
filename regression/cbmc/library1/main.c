struct _IO_FILE;
typedef struct _IO_FILE FILE;
struct _IO_FILE
{
  char dummy;
};

extern FILE *fopen(char const *fname, char const *mode);

int main()
{
  FILE *f;
  f = fopen("some_file", "r");
  __CPROVER_assert(f == 0, "");
  return 0;
}

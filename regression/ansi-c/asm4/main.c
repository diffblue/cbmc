// from Fedora's glibc
struct dirent
{
  int dummy;
};

struct dirent64
{
  int dummy;
};

#ifdef __GNUC__
extern struct dirent *readdir(void *__dirp) __asm__(
  ""
  "readdir64");
extern struct dirent64 *readdir64(void *__dirp);
#endif

int main()
{
#ifdef __GNUC__
  int x;
  (void)readdir(&x);
#endif
  return 0;
}

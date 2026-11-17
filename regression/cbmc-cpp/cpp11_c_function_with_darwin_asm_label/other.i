// as Apple's <stdio.h> declares fopen: the label is Darwin's spelling of
// the name in object files (a leading underscore), so it names this
// function
struct file
{
  int fd;
};
struct file *open_file(const char *name) __asm("_" "open_file");
struct file *open_file(const char *name)
{
  static struct file f;
  f.fd = name[0];
  return &f;
}

// N5008 [filebuf.members]/2-4: opening a file may fail, and open returns a
// null pointer then.  The shape of the MSVC STL: basic_filebuf opens with
// _Fiopen and takes the FILE's buffer pointers from the UCRT's
// _get_stream_buffer_pointers; _Lockit guards the locale machinery.  All
// are defined in the runtime library.
extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void *malloc(decltype(sizeof(0)));
typedef struct _iobuf
{
  void *_Placeholder;
} FILE;
extern "C" int _get_stream_buffer_pointers(
  FILE *_Stream,
  char ***_Base,
  char ***_Pointer,
  int **_Count);
namespace std
{
FILE *_Fiopen(const char *, int, int);
struct _Lockit
{
  explicit _Lockit(int);
  ~_Lockit();
};
} // namespace std
int main()
{
  std::_Lockit lock(0);
  FILE *f = std::_Fiopen("out.txt", 2, 64);
  if(f != nullptr)
  {
    char **base = nullptr;
    char **next = nullptr;
    int *count = nullptr;
    const int r = _get_stream_buffer_pointers(f, &base, &next, &count);
    __CPROVER_assert(
      r == 0 && *base == nullptr && *next == nullptr && *count == 0,
      "empty stream buffer");
  }
  __CPROVER_assert(f != nullptr, "WRONG (must FAIL)");
  return 0;
}

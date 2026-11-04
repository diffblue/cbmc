// the Universal CRT's locale types (corecrt.h) and an inline function of
// stdio.h, which C++ code and the C library models both define
typedef struct locale_pointers
{
  struct locale_data *locinfo;
} locale_pointers;
typedef locale_pointers *locale_handle;
#ifdef __cplusplus
extern "C"
{
#endif
  int common(int, locale_handle);
  inline int wrap(int const x, locale_handle const l)
  {
    return common(x, l);
  }
#ifdef __cplusplus
}
#endif

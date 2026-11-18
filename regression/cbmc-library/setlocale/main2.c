#include <locale.h>

int main(void)
{
  // C11 7.11.1.1p7: a null pointer for locale queries the current locale
  setlocale(LC_ALL, (const char *)0);
  return 0;
}

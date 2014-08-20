void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: goto ERROR;
  }
  return;
}
typedef int size_t;
typedef int bool;
char *strchr(const char *s, int c);
char *strrchr(const char *s, int c);
char *strstr(const char *haystack, const char *needle);
char *strncpy (char *dest, const char *src, size_t n);
char *strncpy_ptr (char *dest, const char *src, size_t n);
char *strcpy (char *dest, const char *src);
unsigned strlen(const char *s);
int strncmp (const char *s1, const char *s2, size_t n);
int strcmp (const char *s1, const char *s2);
char *strcat(char *dest, const char *src);
void *memcpy(void *dest, const void *src, size_t n);
int isascii (int c);
int isspace (int c);
int getc ( );
char *strrand (char *s);
int istrrand (char *s);
int istrchr(const char *s, int c);
int istrrchr(const char *s, int c);
int istrncmp (const char *s1, int start, const char *s2, size_t n);
int istrstr(const char *haystack, const char *needle);
char *r_strncpy (char *dest, const char *src, size_t n);
char *r_strcpy (char *dest, const char *src);
char *r_strcat(char *dest, const char *src);
char *r_strncat(char *dest, const char *src, size_t n);
void *r_memcpy(void *dest, const void *src, size_t n);
typedef unsigned int u_int;
typedef unsigned char u_int8_t;
struct ieee80211_scan_entry {
  u_int8_t *se_rsn_ie;
};
typedef int NSS_STATUS;
typedef char fstring[2];
struct sockaddr_un
{
  char sun_path[2 + 1];
};
static int parse_expression_list(char *str)
{
  int start=0, i=-1, j=-1;
  char str2[2];
  if (!str) return -1;
  do {
    i++;
    switch(str[i]) {
    case 0:
      while ((str[start] == ' ') || (str[start] == '\t')) start++;
      if (str[start] == '"') start++;
      j = i-1;
      while ((0 < j) && ((str[j] == ' ') || (str[j] == '\t'))) j--;
      if ((0 < j) && (str[j] == '"')) j--;
      if (start<=j) {
        r_strncpy(str2, str+start, j-start+1);
        __VERIFIER_assert(j - start + 1 < 2);
        str2[j-start+1] = 0;
      } else {
        return -1;
      }
      start = i+1;
    }
  } while (str[i] != 0);
  return 0;
}
int main ()
{
  char A [2 + 2 + 4 +1];
  A[2 + 2 + 4] = 0;
  parse_expression_list (A);
  return 0;
}

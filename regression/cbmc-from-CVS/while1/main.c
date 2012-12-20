void cmp_str(char* s1, char* s2, int n) {

  while ((n > 0) && (*s1 == *s2)) {
    s1++;
    s2++;
    n--;
  }

  assert ((n <= 0) || (*s1 != *s2));
}

char nondet_char();

#define MAX 3

int main () {
  char a[MAX];
  char b[MAX];
  a[0] = 2;
  b[0] = 2;
  
  for (int i = 1; i < MAX; i++) {
    a[i] = nondet_char();
    b[i] = nondet_char();
  }

  cmp_str(a, b, MAX);
  
  return 0;
}

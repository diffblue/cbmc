extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
char __VERIFIER_nondet_char();
unsigned int __VERIFIER_nondet_uint();

int main() {
    int MAX = __VERIFIER_nondet_uint();
    char str1[MAX], str2[MAX];
    int cont, i, j;
    cont = 0;

    for (i=0; i<MAX; i++) {
        str1[i]=__VERIFIER_nondet_char();
    }
 str1[MAX-1]= '\0';

    j = 0;

    for (i = MAX - 1; i >= 0; i--) {
        str2[j] = str1[0];
        j++;
    }

    j = MAX-1;
    for (i=0; i<MAX; i++) {
      __VERIFIER_assert(str1[i] == str2[j]);
   j--;
    }
}

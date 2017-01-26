
int g_var_n;   // is variable

const int g_const_n = 4;

void body_func(void) {
  g_var_n --;
}

void nobody_func(void); // maybe update 'g_var_n'

void main(void) {
  int i;

  for (i=0; i<g_const_n; i++) { // 0: expected  4
     ;
  }

  g_var_n = g_const_n;
  for (i=0; i<g_var_n; i++) {  // 1: expected -1 (exactly 2)
    body_func();
  }

  g_var_n = g_const_n;
  for (i=0; i<g_var_n; i++) {  // 2:  expected -1
    nobody_func();
  }
}


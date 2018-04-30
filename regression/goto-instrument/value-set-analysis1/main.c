int main(int argc, char** argv) {

  int x;
  int *y = &x;

  g(y, argc);

}

void f() {

  int z;
  int *w = &z;

}

void g(int *param, int unknown) {

  int z;
  int *w = unknown == 5 ? &z : param;

}

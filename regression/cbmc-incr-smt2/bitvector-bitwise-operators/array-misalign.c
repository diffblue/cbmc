
int main() {
  int x[3];
  x[0] = 0;
  x[1] = 0;
  x[2] = 0;
  char *c = x;
  c[1] = 1;
  assert(x[0] == 256);
  assert(x[0] == 0);
  assert(x[1] == 0);
  assert(x[2] == 0);
}

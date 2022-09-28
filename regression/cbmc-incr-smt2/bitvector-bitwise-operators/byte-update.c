
int main() {
  int x;
  char *y = &x;
  y[1] = 1;
  assert(y[1] == 1);
}

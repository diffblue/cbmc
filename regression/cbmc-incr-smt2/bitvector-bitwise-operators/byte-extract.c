
int main() {
  int x;
  char *y = &x;
  assert(y[0] == 0);
}

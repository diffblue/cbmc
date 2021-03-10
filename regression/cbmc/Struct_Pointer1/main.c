struct tag1 {
  int f;
};

int main() {
  struct tag1 x;
  struct tag1 *px;

  px = &x;
  px->f = 0;
  (*px).f = 0;
}

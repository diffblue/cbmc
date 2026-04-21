int main() {
  struct
  {
    int a, b;
  } s, q = {0};

  s=q;

  assert(s.a==q.a);
}

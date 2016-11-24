int main() {
  struct
  {
    int a, b;
  } s, q;

  s=q;

  assert(s.a==q.a);
}

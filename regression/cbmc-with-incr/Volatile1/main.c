volatile int x;
int main() {
  if (!x)
    assert(!x);
}


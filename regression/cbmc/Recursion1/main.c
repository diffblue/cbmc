void f(int counter) {
  if(counter==0) return;

  f(counter-1);
}

int main() {

  f(10);

}

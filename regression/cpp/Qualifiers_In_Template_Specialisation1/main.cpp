template <class T>
class c {
  void fun (const T &arg);
};

template <>
void c<long int>::fun (const long int &arg) { return; }

int main(void) {
  c<long int> cl;

  cl.fun();

  return 0;
}


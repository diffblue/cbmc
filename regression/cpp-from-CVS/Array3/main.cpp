struct C
{
  static const char * array[1];
};

const char * C::array[1] = { "HELLO" };

int main(int argc, const char* argv[])
{
  assert(*C::array[0] == 'H');
}

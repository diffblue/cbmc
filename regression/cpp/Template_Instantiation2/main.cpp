template <typename T>
class c {
public :
  int f00 (const T*);
};

template<>
int c<char>::f00(const char*);

int main(int argc, char* argv[])
{
  return 0;
}

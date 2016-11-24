template <class T>
class bitVector {
 int maxWidth (void) {
    return sizeof(T)*8;
  }
};

//#define WORKS
#ifdef WORKS

typedef bitVector<int> sbv;
typedef bitVector<unsigned int> ubv;

#else

class traits {
  typedef bitVector<int> sbv;
  typedef bitVector<unsigned int> ubv;
};

#endif

int main (void) {
  return 0;
}

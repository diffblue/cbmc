// C++11
// decltype is a C++11 feature to get the "declared type" of an expression.
// It is similar to 'typeof' but handles reference types "properly".

template <class A, class B>
struct whatever {
  int f00 (const B b) {
    typedef  decltype(static_cast<A>(b)) T;
    T z;
    return 1;
  }
};

whatever<int, float> thing;

int main()
{
}

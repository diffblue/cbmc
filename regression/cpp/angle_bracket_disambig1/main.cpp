// Angle bracket disambiguation: < and > as comparison vs template
template <typename T>
struct traits
{
  static const T min_val = 0;
  static const T max_val = 100;
};
typedef long TRet;

bool check(TRet val)
{
  return val < TRet(traits<int>::min_val) || val > TRet(traits<int>::max_val);
}

int main()
{
  bool b = check(50);
  return 0;
}

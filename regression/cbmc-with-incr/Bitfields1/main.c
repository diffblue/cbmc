typedef int INT;

typedef enum _INTEL_CACHE_TYPE {
    IntelCacheNull,
    IntelCacheTrace=10
} INTEL_CACHE_TYPE;

struct bft {
  unsigned int a:3;
  unsigned int b:1;

  // an anonymous bitfield
  signed int :2;
  
  // with typedef
  INT x:1;
  
  // made of sizeof
  unsigned int abc: sizeof(int);

  // enums are integers!
  INTEL_CACHE_TYPE Type : 5;
  
  // and good as field sizes
  INTEL_CACHE_TYPE Field2 : IntelCacheTrace;
};
 

int main() {
  struct bft bf;
   
  assert(bf.a<=7);
  assert(bf.b<=1);
  
  bf.Type=IntelCacheTrace;
}

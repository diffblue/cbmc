typedef signed char int8_t;

struct FIRST {
   int (*get)();
   int8_t (*isEmpty)(int8_t);
};

struct FIRST aVar;
struct FIRST anotherVar;

int aFun(int a) {
 return 0;
}

int main() {
   // type mismatch on arguments and return type
   aVar.isEmpty = &aFun;
   int x = aVar.isEmpty(1);
}

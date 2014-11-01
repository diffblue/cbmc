typedef enum ___strength {
  strength__NONE
} strength;

void execute(void **arguments) {
  if ( (*((strength*)((arguments[0])))) != 1 ) {
    assert(0);
  }
}

int main()
{
  int const  _event_arg = 1;
  void *(___args[1]) = {&_event_arg};
  execute(___args);
}


public class Test {

  public static void main(boolean unknown, boolean other_unknown) {

    int total = 0;

    for(int i = 0; i < 10; ++i) {
      if(unknown)
        total += Other.x;
      else if(other_unknown)
        total -= Third.x;
    }

  }

}

class Other {

  static int x = 1;

}

class Third {

  static int x = 1;

}

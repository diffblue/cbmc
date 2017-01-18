
public class Break {

  public static void main() {

    int j = 0;
    ++j;
    for(int i = 0; i < 10; ++i)
      if(i == 5) break;
    for(j = 0; j < 10; ++j)
      if(j == 5) break;
  }

}

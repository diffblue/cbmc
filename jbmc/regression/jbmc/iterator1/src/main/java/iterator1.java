import java.util.List;

public class iterator1
{
  public void f(List<String> list)
  {
    int i = 0;
    for(String s : list)
      i++;

    assert false;
  }
}

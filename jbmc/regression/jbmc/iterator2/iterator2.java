import java.util.List;

public class iterator2
{
  public void f(List<List<String>> list)
  {
    int i = 0, j = 0;
    for(List<String> l : list) 
    {
      for(String s : l)
        i++;
    }
    for(j=0;j<i;j++);
    assert false;
  }
}

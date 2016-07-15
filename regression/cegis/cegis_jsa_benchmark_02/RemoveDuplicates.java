import java.util.*;

public class RemoveDuplicates {
  public static removeDuplicates(LinkedList<Integer> list) {
    HashMap<Integer, Integer> occurences = new HashMap<Integer, Integer>();

    Iterator it = list.iterator();
    while(it.hasNext()) {
      Integer i = (int) it.next();
      if (occurences.containsKey(i))
        
    }
  }
}
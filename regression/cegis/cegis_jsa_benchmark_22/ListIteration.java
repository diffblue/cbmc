import java.util.*;

public class ListIteration {
    public static void main(String[] args) {
        List<Integer> l = new LinkedList<Integer>();
        ListIterator<Integer> it = l.listIterator();
        while(it.hasNext()) { 
            it.next(); 
            it.set(5); 
        }
    }
}
    
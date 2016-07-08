package bynull.collections;

import java.util.*;

/**
 * Created by null on 5/4/14.
 */
public class CollectionFilter {

    public static void main(String[] args) {
        List<Integer> list = new ArrayList<Integer>(Arrays.asList(1, 2, 3, 4, 5, 6, 7, 8, 9));

        int counter = 0;
        for (Integer currChiper : list) {
            counter++;
            if (counter == 5) {
                filterCollection(list);
            }
        }

        System.out.println(list);
    }

    private static void filterCollection(List<Integer> list) {
        for (ListIterator<Integer> it = list.listIterator(); it.hasNext(); ) {
            if (it.next() > 6) {
                it.remove();
            }
        }
    }
}

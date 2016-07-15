import java.util.*;
import java.lang.*;

public class ExerciseThree {
	public static void main(String[] args) {
		Integer[] numbers = {7, 2, 5, 9, 4, 10, 21, 31, 6, 19, 2, 32, 21};
		LinkedList<Integer> list = new LinkedList<Integer>(Arrays.asList(numbers));
		
		for (int i=0; i<list.size(); i++) {
			if (list.get(i) % 2 == 0)
				list.remove(i);
			System.out.println(list);
		}
		
		System.out.println();
		// Magic for loop commented out because it throws exception
		/**
		list = new LinkedList<Integer>(Arrays.asList(numbers));
		for (Integer i : list) {
			if (list.get(i) % 2 == 0)
				list.remove(i);
			System.out.println(list);
		}
		**/
		
		list = new LinkedList<Integer>(Arrays.asList(numbers));
		ListIterator<Integer> iterator = list.listIterator();
		while (iterator.hasNext()) {
			Integer i = iterator.next();
			if (i % 2 == 0)
				iterator.remove();
			System.out.println(list);
		}
		
		System.out.println();
		
		PriorityQueue<Integer> queue = new PriorityQueue<Integer>(Arrays.asList(numbers));
		Iterator<Integer> it = queue.iterator();
		while (it.hasNext()) {
			System.out.println(queue.poll());
			System.out.println(queue);
		}
		
	}
}
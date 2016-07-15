import java.util.Iterator;
import java.util.LinkedList;
import java.util.Scanner;

public class IteratorMain {

	public static void main(String[] args) {

		Scanner in = new Scanner(System.in);
		LinkedList<Integer> list = new LinkedList<Integer>();

		for (int i = 0; i < 100000; i++) {
			list.add((int) (Math.random() * 99 + 1));
		}
		System.out.println("Your list is: ");
		System.out.println(list);
		System.out.println("Which number you want to remove? ");
		Integer num = in.nextInt();
		in.close();

		Iterator<Integer> it = list.iterator();
		while (it.hasNext()) {
			Integer number = it.next();
			if (number % num == 0) {
				it.remove();
			}
		}

		System.out.println();
		System.out.println(list);
	}

}

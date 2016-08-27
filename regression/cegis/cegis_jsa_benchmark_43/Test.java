import java.util.ArrayList;
import java.util.Arrays;



public class Test {
	public static void main(String[] args) {
		ArrayList<Integer> list1 = new ArrayList<Integer>(Arrays.asList(1, 2, 3));
		ArrayList<Integer> list2 = new ArrayList<Integer>(Arrays.asList(6, 1, 3, 5, 2, 8, 9));
		for (int i = 0; i < list1.size(); i++) {
			for (int j = 0; j < list2.size(); j++) {
				if (list2.get(j) == list1.get(i)) {
					list2.remove(j);
					break;
				}
			}
		}
		System.out.println(list2);
	}
}

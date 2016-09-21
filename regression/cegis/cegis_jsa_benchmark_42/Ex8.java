package Week3;

import java.util.ArrayList;

public class Ex8 {
	public static void main(String[] args) {
		ArrayList<ArrayList<Integer>> l = new ArrayList<ArrayList<Integer>>();

		ArrayList<Integer> l1 = new ArrayList<Integer>();
		l1.add(1);
		l1.add(2);

		ArrayList<Integer> l2 = new ArrayList<Integer>();
		l2.add(1);
		l2.add(1);

		l.add(l1);
		l.add(l2);
		
		ArrayList<ArrayList<Integer>> newList = findNum(l, 2);


		for(ArrayList<Integer> print : l) {
			for(Integer printInt : print) {
				System.out.println(printInt);
			}
		}
	}

	public static ArrayList<ArrayList<Integer>> findNum(ArrayList<ArrayList<Integer>> list, int num) {
		
		for(ArrayList<Integer> l1 : list) {

			for(Integer l2 : l1) {
				if(l2 == 2) {
					list.remove(l1);
					break;
				}
			}
		}
		return list;
	}
	
	public static void remove(ArrayList<Integer> l) {
		
		
	}
}

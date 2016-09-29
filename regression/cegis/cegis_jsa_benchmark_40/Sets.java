import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

//SRM 159 DIV 2 - 500 points
public class Sets {

	public int[] operate(int[] A, int[] B, String operation) {
		List<Integer> a = new ArrayList<Integer>();
		for (int i : A) {
			a.add(i);
		}
		List<Integer> b = new ArrayList<Integer>();
		for (int i : B) {
			b.add(i);
		}
		List<Integer> result = null;
		switch (operation) {
			case "UNION": result = union(a, b); break;
			case "INTERSECTION": result = intersection(a, b); break;
			case "SYMMETRIC DIFFERENCE": result = difference(a, b); break;
		}
		if(result != null) {
			int[] intArray = new int[result.size()];
			for (int i = 0; i < intArray.length; i++) {
			    intArray[i] = result.get(i);
			}
			return intArray;
		}
		return null;
	}

	private List<Integer> union(List<Integer> A, List<Integer> B) {
		List<Integer> result = new ArrayList<Integer>();
		for (int a : A) {
			if (!result.contains(a)) {
				result.add(a);
			}
		}
		for (int b : B) {
			if (!result.contains(b)) {
				result.add(b);
			}
		}
		Collections.sort(result);
		return result;
	}

	private List<Integer> intersection(List<Integer> A, List<Integer> B) {
		List<Integer> result = new ArrayList<Integer>();
		for (int a : A) {
			if (!result.contains(a) && B.contains(a)) {
				result.add(a);
			}
		}
		Collections.sort(result);
		return result;
	}

	private List<Integer> difference(List<Integer> A, List<Integer> B) {
		List<Integer> result = new ArrayList<Integer>();
		for (int a : A) {
			if (!result.contains(a) && !B.contains(a)) {
				result.add(a);
			}
		}
		for (int b : B) {
			if (!result.contains(b) && !A.contains(b)) {
				result.add(b);
			}
		}
		Collections.sort(result);
		return result;
	}
}

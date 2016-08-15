import java.util.*; 
import java.util.LinkedList; 

public class Npeople {
	public static void main(String[] args) {
		new Npeople().go();
	}

	public void go() {
		List<Integer> people = fill(new ArrayList<Integer>(), 10);
		List<Integer> piople = fill(new LinkedList<Integer>(), 10);
		removePeopleFor(people);
		removePeople(piople);

	}

	public List<Integer> fill(List<Integer> l, int n) {
		for (int i = 0; i < n; i++) {
			l.add(i);
		}
		return l;
	}

	public void removePeople(List<Integer> l) {
		while (l.size() > 1) {
			Iterator<Integer> it = l.iterator();
			int i = 0;
			while (it.hasNext()) {

				Integer el = it.next();
				if ((i % 2) == 0) {
					it.remove();
					System.out.println(el + " removed");
				}
				i++;
			}
		}
	}

	public void removePeopleFor(List<Integer> l) {
		while (l.size() > 1) {
			int n = l.size();
			for (int i = n - 1; i >= 0; i--){
				if ((i % 2) == 0) {
					Integer s = l.remove(i);
					System.out.println(s + "removed");
				}
			}
		}
	}
}
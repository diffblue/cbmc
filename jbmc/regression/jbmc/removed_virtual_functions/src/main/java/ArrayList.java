public class ArrayList<E> extends AbstractList<E>
    implements List<E>
{
    public ListIterator<E> listIterator() {
        return new ListItr(0);
    }
    public ListIterator<E> listIterator(int index) {
        return new ListItr(index);
    }
    private class ListItr extends Itr implements ListIterator<E> {
        ListItr(int index) {
            super();
        }

        public boolean hasPrevious() {
            return false;
        }
    }

    private class Itr implements Iterator<E> {
        Itr() {
        }

        public boolean hasNext() {
            return false;
        }
        public E next() {
            return null;
        }
    }
}

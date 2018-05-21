public interface List<E> {
    ListIterator<E> listIterator();
    ListIterator<E> listIterator(int index);
}

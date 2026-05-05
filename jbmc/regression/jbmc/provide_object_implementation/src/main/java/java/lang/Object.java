package java.lang;

public class Object {
    public final Class<?> getClass() {
      return null;
    }

    public int hashCode() { return 0; }

    public boolean equals(Object obj) { return (this == obj); }

    protected Object clone() throws CloneNotSupportedException {
      throw new CloneNotSupportedException();
    }

    public String toString() { return "object"; }

    public final void notify() {}

    public final void notifyAll() {}

    public final void wait(long timeout) throws InterruptedException {
      throw new InterruptedException();
    }

    public final void wait(long timeout, int nanos) throws InterruptedException {
        wait(timeout);
    }

    public final void wait() throws InterruptedException { wait(0); }

    protected void finalize() throws Throwable { }
}

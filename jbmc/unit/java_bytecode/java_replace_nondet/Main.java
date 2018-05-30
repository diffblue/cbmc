public class Main {
    public void replaceNondetAssignment() {
        Object temp = org.cprover.CProver.nondetWithoutNull();
    }

    public void replaceNondetAssignmentUnbox() {
        int temp = org.cprover.CProver.nondetWithoutNull();
    }

    public void replaceNondetAssignmentImplicitCast() {
        Integer temp = org.cprover.CProver.nondetWithoutNull();
    }

    public void replaceNondetAssignmentExplicitCast() {
        Integer temp = (Integer)org.cprover.CProver.nondetWithoutNull();
    }

    public void replaceNondetAssignmentAddition() {
        int temp = ((int)org.cprover.CProver.nondetWithoutNull()) + 3;
    }

    public void replaceNondetUnused() {
        org.cprover.CProver.nondetWithoutNull();
    }

    public int replaceNondetReturnUnboxed() {
        return org.cprover.CProver.nondetWithoutNull();
    }

    public Object replaceNondetReturn() {
        return org.cprover.CProver.nondetWithoutNull();
    }

    public Integer replaceNondetReturnWithImplicitCast() {
        return org.cprover.CProver.nondetWithoutNull();
    }

    public Integer replaceNondetReturnWithExplicitCast() {
        return (Integer)org.cprover.CProver.nondetWithoutNull();
    }

    public Integer replaceNondetReturnAddition() {
        return ((int)org.cprover.CProver.nondetWithoutNull()) + 3;
    }
}

public class AssertionIssue {

    public static void throwAssertion() {
        throw new AssertionError("Something went terribly wrong.", new ThrowableAssertion());
    }

    public static class ThrowableAssertion extends Throwable {
        @Override
        public String getMessage() {
            return "How did we get here?";
        }
    }
}

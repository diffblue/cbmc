import org.cprover.CProver;

/**
 * Example: Verifying a simple banking operation
 *
 * This example demonstrates the use of assertions, non-determinism,
 * and assumptions in JBMC verification.
 */
public class BankingExample {

    /**
     * Transfer money from one account to another
     * @param fromBalance - source account balance
     * @param amount - amount to transfer
     * @return true if transfer succeeded, false otherwise
     */
    public static boolean transfer(int fromBalance, int amount) {
        if (amount <= 0) {
            return false;  // Invalid amount
        }
        if (fromBalance < amount) {
            return false;  // Insufficient funds
        }
        // Transfer successful
        return true;
    }

    /**
     * Verification harness for the transfer function
     */
    public static void verifyTransfer() {
        // 1. NON-DETERMINISM: Create arbitrary inputs
        int fromBalance = CProver.nondetInt();
        int amount = CProver.nondetInt();

        // 2. ASSUMPTIONS: Constrain inputs to valid ranges
        // Balances must be non-negative
        CProver.assume(fromBalance >= 0);
        // Amount must be reasonable (prevent overflow)
        CProver.assume(amount >= 0 && amount <= 1000000);

        // Call the function under test
        boolean result = transfer(fromBalance, amount);

        // 3. ASSERTIONS: Verify expected properties

        // Property 1: Transfer fails for non-positive amounts
        if (amount <= 0) {
            assert !result : "transfer should fail for non-positive amount";
        }

        // Property 2: Transfer fails for insufficient funds
        if (amount > 0 && fromBalance < amount) {
            assert !result : "transfer should fail for insufficient funds";
        }

        // Property 3: Transfer succeeds when conditions are met
        if (amount > 0 && fromBalance >= amount) {
            assert result : "transfer should succeed when funds are sufficient";
        }
    }

    /**
     * Example with object non-determinism
     */
    public static void verifyWithObjects() {
        // Create non-deterministic String that might be null
        String message = CProver.nondetWithNull(null);

        // Assume it's non-null for this test
        CProver.assume(message != null);

        // Now we can safely use the string
        int length = message.length();
        assert length >= 0 : "string length is non-negative";
    }

    public static void main(String[] args) {
        // Run verification harnesses
        verifyTransfer();
        verifyWithObjects();
    }
}

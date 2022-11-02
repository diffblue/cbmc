## Proof Harness Intrumentation {#contracts-dev-spec-harness}

Back to top @ref contracts-dev-spec

@tableofcontents

The harness function is the entry point of the analysis and is meant to contain a direct or indirect call to the function being checked against a contract or potentially several functions replaced by contracts. The harness can also contain preamble instructions to set up proof assumptions or perform cleanup after the call to the checked function. We do not want to check these functions and instructions against any particular write set.  Instrumenting a harness function just consists in passing a NULL value for the write_set parameter to all function and function pointer calls it contains. This will result in no write_set updates or checks being performed in the harness or in the functions called directly from the harness (and transitively in functions they call). One of the functions called directly (or indirectly) by the harness is eventually going to be a wrapper function that checks the contract against the function of interest. This wrapper will ignore the NULL write set it received from the harness and instantiate its own local write set from the contract and pass it to the function under analysis. This will trigger cascading checks in all functions called from the checked function thanks to the propagation of the write set through function calls and function pointer calls.

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-dfcc | @ref contracts-dev-spec-contract-checking
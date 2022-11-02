# Code Contracts in CBMC {#contracts-mainpage}

Code contracts in CBMC provide way to safely abstract parts of a program,
typically in order to accelerate the verification process.
The key idea is to overapproximate the possible set of program states,
while still being precise enough to be able to prove the desired property.

To learn more about contracts, take a look at the chapter [Design by
Contract](http://se.inf.ethz.ch/~meyer/publications/old/dbc_chapter.pdf) from
the book Object-Oriented Software Construction by Bertrand Meyer or read the
notes [Contract-based
Design](https://www.georgefairbanks.com/york-university-contract-based-design-2021)
by George Fairbanks.

For extra steps required to compositionally reason about file-local functions
[please consult this link](todo-link-to-cprover-manual-static-functions).

- @subpage contracts-user
- @subpage contracts-dev

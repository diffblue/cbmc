# The CPROVER C++ API

This folder includes the interface and the implementation of a new C++-based
API for the CProver libraries. This allows direct linking to key CProver functionality
via C++ function calls. This (will eventually) allow the use of all aspects of
the CProver verification pipeline via direct function calls and deprecate the
need for invoking separate tools/programs.

## Implementation

The major part of the implementation of the API is in [`api.cpp`](src/api.cpp).
To use the API as it stands, you need to include the header [`api.h`](src/api.h)
in your program, and link against the resultant shared-object from the CProver
build process (`libcprover-api.a`).

## Example

An example for driving the API in its current form is in the file [`call_bmc.cpp`](regression/call_bmc.cpp),
which we are also using as a binary driver for testing the API.

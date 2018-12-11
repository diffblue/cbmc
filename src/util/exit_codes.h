/*******************************************************************\

Module: Exit codes

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXIT_CODES_H
#define CPROVER_UTIL_EXIT_CODES_H

/// \file
/// Document and give macros for the exit codes of CPROVER binaries.

/// Success indicates the required analysis has been performed without error.
#define CPROVER_EXIT_SUCCESS 0
// should contemplate EX_OK from sysexits.h

/// Verification successful indicates the analysis has been performed without
/// error AND the software is safe (w.r.t. the current analysis / config / spec)
#define CPROVER_EXIT_VERIFICATION_SAFE 0

/// Verification successful indicates the analysis has been performed without
/// error AND the software is not safe (w.r.t. current analysis / config / spec)
#define CPROVER_EXIT_VERIFICATION_UNSAFE 10

/// Verification inconclusive indicates the analysis has been performed without
/// error AND the software is neither safe nor unsafe
/// (w.r.t. current analysis / config / spec)
#define CPROVER_EXIT_VERIFICATION_INCONCLUSIVE 5

/// A usage error is returned when the command line is invalid or conflicting.
#define CPROVER_EXIT_USAGE_ERROR 1
// should contemplate EX_USAGE from sysexits.h

/// An error during parsing of the input program
#define CPROVER_EXIT_PARSE_ERROR 2
// This should be the same as YY_EXIT_FAILURE

/// An (unanticipated) exception was thrown during computation.
#define CPROVER_EXIT_EXCEPTION 6
// should contemplate EX_SOFTWARE from sysexits.h
#define CPROVER_EXIT_EXCEPTION_GOTO_INSTRUMENT 11

/// An error has been encountered during processing the requested analysis.
#define CPROVER_EXIT_INTERNAL_ERROR 6

/// The command line is correctly structured but cannot be carried out
/// due to missing files, invalid file types, etc.
#define CPROVER_EXIT_INCORRECT_TASK 6

/// Memory allocation has failed and this has been detected within the program.
#define CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY 6

/// Failure to identify the properties to verify
#define CPROVER_EXIT_SET_PROPERTIES_FAILED 7
// should contemplate EX_USAGE from sysexits.h

/// Failure of the test-preprocessor method
#define CPROVER_EXIT_PREPROCESSOR_TEST_FAILED 8

/// Failure to convert / write to another format
#define CPROVER_EXIT_CONVERSION_FAILED 10

#endif // CPROVER_UTIL_EXIT_CODES_H

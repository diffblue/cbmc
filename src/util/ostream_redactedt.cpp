/*******************************************************************\

Module: ostream_redactedt

Author: Diffblue

Date: Oct 2018

\*******************************************************************/
#include "ostream_redactedt.h"

ostream_redactedt ostream_redacted_cout(std::cout);
ostream_redactedt ostream_redacted_cerr(std::cerr);

ostream_redactedt ostream_redact_off_cout(std::cout, false);
ostream_redactedt ostream_redact_off_cerr(std::cerr, false);
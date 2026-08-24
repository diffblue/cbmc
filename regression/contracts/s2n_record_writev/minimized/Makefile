PROJECT_NAME = "s2n"

CHECKFLAGS += --pointer-primitive-check


LITANI ?= litani

PROOFDIR ?= $(abspath .)


CBMC_OBJECT_BITS = 9
PROOF_UID = s2n_record_writev
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOF_UID).c

# CHECK_FUNCTION_CONTRACTS += s2n_record_writev
# USE_FUNCTION_CONTRACTS += s2n_hmac_update

PROJECT_SOURCES += $(PROOFDIR)/$(HARNESS_FILE)
PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE)


include Makefile.common

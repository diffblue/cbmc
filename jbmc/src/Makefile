DIRS = jbmc java_bytecode miniz

include config.inc

.PHONY: all
all: jbmc.dir

# building cbmc proper
.PHONY: cprover.dir
cprover.dir:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR)/src

.PHONY: java_bytecode.dir
java_bytecode.dir: miniz.dir

.PHONY: jbmc.dir
jbmc.dir: java_bytecode.dir cprover.dir

.PHONY: miniz.dir
miniz.dir:

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# generate source files

$(patsubst %, %_generated_files, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_generated_files, %, $@) generated_files

.PHONY: generated_files
generated_files: $(patsubst %, %_generated_files, $(DIRS))

# cleaning

.PHONY: clean
clean: $(patsubst %, %_clean, $(DIRS)) cprover_clean

$(patsubst %, %_clean, $(DIRS)):
	$(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \

.PHONY: cprover_clean
cprover_clean:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR)/src clean

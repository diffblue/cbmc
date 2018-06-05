.NOTPARALLEL:
#javac compiles multiple classes for each source as it will compile dependent sources.
#Thus we do not allow the make to run concurrently.

include ../../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

SOURCE_DIR := src/main/java
BINARY_DIR := classes

FIND := find

JAVAC := javac
JFLAGS := -sourcepath $(SOURCE_DIR) -d $(BINARY_DIR) -XDignore.symbol.file

CLASSPATH := SOURCE_DIR

ALL_JAVAS := $(wildcard $(SOURCE_DIR)/*/*.java $(SOURCE_DIR)/*/*/*.java $(SOURCE_DIR)/*/*/*/*.java)
ALL_CLASSES := $(patsubst $(SOURCE_DIR)/%.java,$(BINARY_DIR)/%.class,$(ALL_JAVAS))

$(BINARY_DIR):
	mkdir -p $(BINARY_DIR)

.SUFFIXES: .java .class

$(BINARY_DIR)/%.class: $(SOURCE_DIR)/%.java $(BINARY_DIR)
	$(JAVAC) $(JFLAGS) $(patsubst $(BINARY_DIR)/%.class,$(SOURCE_DIR)/%.java,$@)

JAR := jar
JARFLAGS := -cf

core-models.jar: $(ALL_CLASSES)
	$(JAR) $(JARFLAGS) $@ -C $(BINARY_DIR) .

CLEANFILES = core-models.jar

all: core-models.jar

clean: clean_

clean_:
	$(RM) -Rf $(BINARY_DIR)

.NOTPARALLEL:
#javac compiles multiple classes for each source as it will compile dependent sources.
#Thus we do not allow the make to run concurrently.

SRC = converter.cpp

include ../../config.inc
include ../../common

SOURCE_DIR := src
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

CLEANFILES = core-models.jar converter$(EXEEXT) java_core_models.inc

all: java_core_models.inc

clean: clean_

clean_:
	$(RM) -Rf $(BINARY_DIR)

converter$(EXEEXT): converter.cpp
	$(LINKNATIVE)

java_core_models.inc: converter$(EXEEXT) core-models.jar
	./converter$(EXEEXT) JAVA_CORE_MODELS core-models.jar > $@

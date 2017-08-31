all: org.cprover.jar

SOURCE_DIR := src
BINARY_DIR := classes

FIND := find

JAVAC := javac
JFLAGS := -sourcepath $(SOURCE_DIR) -d $(BINARY_DIR)

CLASSPATH := SOURCE_DIR

all_javas := $(shell $(FIND) $(SOURCE_DIR) -name '*.java')

$(BINARY_DIR):
	mkdir -p $(BINARY_DIR)

.PHONY: compile
compile: $(BINARY_DIR)
	$(JAVAC) $(JFLAGS) $(all_javas)

JAR := jar
JARFLAGS := -cf

org.cprover.jar: compile
	$(JAR) $(JARFLAGS) $@ -C $(BINARY_DIR) org

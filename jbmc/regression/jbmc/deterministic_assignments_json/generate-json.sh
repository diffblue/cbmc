#!/bin/bash

mvn package
java -cp target/jsonGenerator-1.0-SNAPSHOT-jar-with-dependencies.jar:. org.cprover.JsonGenerator
# The following command only works using GNU sed.
# (Remove all lines containing the string "StaticFieldMap" as they are not needed.)
sed -i '/StaticFieldMap/d' clinit-state.json

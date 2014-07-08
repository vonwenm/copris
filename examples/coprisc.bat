#!/bin/sh
DIR=`dirname $0`/..
JARS=$DIR/build/copris-all-v2-2-4.jar:$DIR/lib/jsr331/"*"
[ -z "$JSR331" ] || JARS=$DIR/build/copris-all-v2-2-4.jar:$JSR331:$DIR/lib/jsr331/"*"
[ -n "$JAVA_OPTS" ] || export JAVA_OPTS="-Xmx2G -Xms512M -Xss64M"
exec scalac -optimize -cp .:$JARS -d classes $*
# exec fsc -optimize -cp .:classes:$JARS -d classes $*

VER = v2-2-5
VERSION = 2.2.5

APP0 = copris
APP = $(APP0)-$(VER)
JAR = $(APP).jar
JARALL = $(APP0)-all-$(VER).jar
ZIP = $(APP).zip
SUGAR = lib/sugar-v2-2-1.jar
SAT4J = lib/org.sat4j.core.jar
JSR331 = lib/jsr331/jsr331.jar lib/jsr331/log4j-1.2.15.jar lib/jsr331/commons-logging-1.1.jar lib/jsr331/commons-logging-api-1.1.jar
PROPERTIES = log4j.properties
JARS = $(SUGAR):$(SAT4J):lib/jsr331/"*"
SRCS = src/jp/kobe_u/*.scala src/jp/kobe_u/copris/*.scala src/jp/kobe_u/copris/*/*.scala
DOCS = docs/LICENSE.txt docs/CHANGES.html docs/CHANGES.org docs/api
INCLUDES = Makefile src/ examples/ $(PROPERTIES)
WEBPAGE = http://bach.istc.kobe-u.ac.jp/copris/
WEBTITLE = Copris: Constraint Programming in Scala

DOCTITLE = Copris version $(VERSION) Core API Specification
SCALADOC  = scaladoc \
	-d docs/api \
	-doc-title '$(DOCTITLE)' \
	-doc-version '$(VERSION)' \
	-classpath $(JAR):$(JARS) \
	-sourcepath src

all: jar scaladoc zip

jar: build/$(JAR) build/$(JARALL)

scaladoc: docs/api/index.html

zip: build/$(ZIP)

build/$(JAR): $(SRCS) $(SUGAR) $(SAT4J) $(JSR331)
	mkdir -p build
	mkdir -p classes
	rm -rf classes/*
	fsc -reset
	fsc -sourcepath src -d classes -cp $(JARS) -optimise $(SRCS)
	jar cf build/$(JAR) -C classes .
	jar uf build/$(JAR) $(PROPERTIES)
	jar uf build/$(JAR) meta-inf
	rm -rf classes/*

build/$(JARALL): build/$(JAR)
	cd classes; jar xf ../build/$(JAR) jp
	cd classes; jar xf ../$(SUGAR) jp
	cd classes; jar xf ../$(SAT4J)
	cd classes; rm -rf META-INF meta-inf
	cd classes; jar cf ../build/$(JARALL) *
	jar uf build/$(JARALL) $(PROPERTIES)
	rm -rf classes/*	

docs/api/index.html: build/$(JAR)
	rm -rf docs/api/*
	$(SCALADOC) $(SRCS)

build/$(ZIP): build/$(JARALL) docs/api/index.html $(INCLUDES) $(DOCS)
	rm -f build/$(ZIP)
	rm -rf $(APP)
	mkdir $(APP) $(APP)/docs
	cp -pr $(INCLUDES) $(APP)
	cp -pr $(DOCS) $(APP)/docs/
	mkdir $(APP)/build; mkdir $(APP)/classes; mkdir $(APP)/lib; mkdir $(APP)/lib/jsr331
	cp -p build/$(JAR) build/$(JARALL) $(APP)/build
	cp -p $(SUGAR) $(SAT4J) $(APP)/lib/
	cp -p $(JSR331) $(APP)/lib/jsr331/
	cp -p $(PROPERTIES) $(APP)/lib/jsr331/
	find $(APP) \( -name .svn -o -name CVS -o -name .cvsignore -o -name '*~' \) -exec rm -r '{}' '+'
	zip -q -r build/$(ZIP) $(APP)
	rm -rf $(APP)

deploy: build/$(ZIP)
	cp -p build/$(ZIP) ../packages/

clean:
	rm -rf classes/*
	rm -rf docs/api/*
	rm build/$(JAR) build/$(JARALL) build/$(ZIP)

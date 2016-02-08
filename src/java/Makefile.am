
JAVA_H = java/include/com_cruzdb_Log.h
BUILT_SOURCES += $(JAVA_H)

NATIVE_JAVA_CLASSES = \
	com.cruzdb.Log

OUTPUT = java/target
MAIN_CLASSES = $(OUTPUT)/classes
TEST_CLASSES = $(OUTPUT)/test-classes
MAIN_SRC = java/src/main/java
TEST_SRC = java/src/test/java
NATIVE_INCLUDE = java/include

# TODO: add dependency on the java source (here and jar)
$(JAVA_H): FORCE
	mkdir -p $(MAIN_CLASSES)
	$(JAVAC) -d $(MAIN_CLASSES) $(MAIN_SRC)/com/cruzdb/*.java
	$(JAVAH) -cp $(MAIN_CLASSES) -d $(NATIVE_INCLUDE) -jni $(NATIVE_JAVA_CLASSES)

FORCE:

lib_LTLIBRARIES += libzlogjni.la
libzlogjni_la_SOURCES = java/native/zlogjni.cc $(JAVA_H)
libzlogjni_la_LIBADD = $(LIBZLOG)
libzlogjni_la_CPPFLAGS = -I$(srcdir)/java/include $(JNI_CPPFLAGS) $(AM_CPPFLAGS)
libzlogjni_la_LDFLAGS = -avoid-version -module -shared -export-dynamic

$(ZLOG_JAR): libzlogjni.la
	cp $(builddir)/.libs/libzlogjni.so java/target
	cd java/target; $(JAR) -cf $(ZLOG_JAR) libzlogjni.so
	cd java/target/classes; $(JAR) -uf ../$(ZLOG_JAR) com/cruzdb/*.class

javadir = $(datadir)/java
java_DATA = $(ZLOG_JAR)

hello: $(ZLOG_JAR) java/ZlogHello.java
	$(JAVAC) -cp java/target/$(ZLOG_JAR) java/ZlogHello.java
	java -cp java/target/$(ZLOG_JAR):java -Xcheck:jni ZlogHello

JAVADOC_DIR = $(OUTPUT)/apidocs

javadocs:
	rm -rf $(JAVADOC_DIR)
	mkdir -p $(JAVADOC_DIR)
	$(JAVADOC) -d $(JAVADOC_DIR) -sourcepath $(MAIN_SRC) -subpackages com

publish: javadocs
	rm -rf /tmp/zlog.javadoc.bits
	mkdir /tmp/zlog.javadoc.bits
	cp -a $(JAVADOC_DIR)/* /tmp/zlog.javadoc.bits
	cd /tmp/zlog.javadoc.bits; \
		git init .; git add .; git commit -m "published"; \
		git remote add origin http://github.com/noahdesu/zlog.git; \
		git push -f origin master:gh-pages
	rm -rf /tmp/zlog.javadoc.bits

JAVA_TEST_LIBDIR = test-libs
JAVA_JUNIT_JAR = $(JAVA_TEST_LIBDIR)/junit-4.12.jar
JAVA_HAMCR_JAR = $(JAVA_TEST_LIBDIR)/hamcrest-core-1.3.jar
JAVA_TESTCLASSPATH = $(JAVA_JUNIT_JAR):$(JAVA_HAMCR_JAR)

test-java-deps:
	test -s "$(JAVA_TEST_LIBDIR)" || mkdir -p "$(JAVA_TEST_LIBDIR)"
	test -s "$(JAVA_JUNIT_JAR)" || curl -k -L -o $(JAVA_JUNIT_JAR) http://search.maven.org/remotecontent?filepath=junit/junit/4.12/junit-4.12.jar
	test -s "$(JAVA_HAMCR_JAR)" || curl -k -L -o $(JAVA_HAMCR_JAR) http://search.maven.org/remotecontent?filepath=org/hamcrest/hamcrest-core/1.3/hamcrest-core-1.3.jar

test-java: $(ZLOG_JAR) test-java-deps
	rm -rf $(TEST_CLASSES)
	mkdir -p $(TEST_CLASSES)
	$(JAVAC) -cp $(JAVA_TESTCLASSPATH):$(OUTPUT)/$(ZLOG_JAR) -d $(TEST_CLASSES) $(TEST_SRC)/com/cruzdb/*.java
	java -ea -Xcheck:jni -cp $(JAVA_TESTCLASSPATH):$(OUTPUT)/test-classes:$(OUTPUT)/$(ZLOG_JAR) com.cruzdb.AllTests com.cruzdb.LogTest

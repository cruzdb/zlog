
JAVA_H = java/include/com_cruzdb_Log.h
BUILT_SOURCES += $(JAVA_H)

NATIVE_JAVA_CLASSES = \
	com.cruzdb.Log

OUTPUT = java/target
MAIN_CLASSES = $(OUTPUT)/classes
MAIN_SRC = java/src/main/java
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

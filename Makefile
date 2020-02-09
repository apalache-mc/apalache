# a good old Makefile for the end users, as Maven is too much pain

DEPDIR=3rdparty
DEPS=$(DEPDIR)/lib/com.microsoft.z3.jar $(DEPDIR)/lib/box.jar

all: apalache

apalache:
	# tell maven to load the binary libraries and build the package
	JAVA_LIBRARY_PATH=$(abspath $(DEPDIR)/lib) mvn package

lib: $(DEPS)
	# install third-party libraries
	cd $(DEPDIR)
	./install-local.sh


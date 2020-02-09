# a good old Makefile for the end users, as Maven is too much pain

DEPDIR=3rdparty
DEPS=$(DEPDIR)/lib/com.microsoft.z3.jar $(DEPDIR)/lib/box.jar

all: apalache

apalache: $(DEPS)
	# tell maven to load the binary libraries and build the package
	JAVA_LIBRARY_PATH=$(abspath $(DEPDIR)/lib) mvn package

integration: apalache
	# unit tests are run by mvn package
	# integration tests are run here
	cd test \
	 && JAVA_LIBRARY_PATH=$(abspath $(DEPDIR)/lib) NO_MVN=1 \
        ./run-integration

$(DEPDIR)/lib/com.microsoft.z3.jar:
	# install microsoft z3
	cd $(DEPDIR) && ./install-local.sh

$(DEPDIR)/lib/box.jar:
	# install box by Jure (fix in the future!)
	cd $(DEPDIR) && ./install-local.sh


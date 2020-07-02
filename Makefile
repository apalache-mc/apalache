# a good old Makefile for the end users, as Maven is too much pain

DEPDIR=3rdparty
DEPS=$(DEPDIR)/lib/com.microsoft.z3.jar $(DEPDIR)/lib/box.jar
ENV=JAVA_LIBRARY_PATH="$(abspath $(DEPDIR)/lib)" NO_MVN=1 LD_LIBRARY_PATH="$(abspath $(DEPDIR)/lib)"

.PHONY: all, apalache, test, integration, clean

all: apalache

apalache: $(DEPS)
	# tell maven to load the binary libraries and build the package
	$(ENV) mvn package

test:
	mvn test

integration: apalache
	# unit tests are run by mvn package
	# integration tests are run here
	cd test \
	 && $(ENV) ./run-integration

clean:
	mvn clean

$(DEPDIR)/lib/com.microsoft.z3.jar:
	# install microsoft z3
	cd "$(DEPDIR)" && ./install-local.sh

$(DEPDIR)/lib/box.jar:
	# install box by Jure (fix in the future!)
	cd "$(DEPDIR)" && ./install-local.sh


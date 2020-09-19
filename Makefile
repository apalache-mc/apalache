# a good old Makefile for the end users, as Maven is too much pain

DEPDIR=3rdparty
DEPS=$(DEPDIR)/lib
ENV=JAVA_LIBRARY_PATH="$(abspath $(DEPDIR)/lib)" NO_MVN=1 LD_LIBRARY_PATH="$(abspath $(DEPDIR)/lib)"

# See https://www.jrebel.com/blog/how-to-speed-up-your-maven-build
#
# - verify:none disables bytecode verification giving a speed boost, but should
#   not be used for releases or productin. See https://blogs.oracle.com/buck/never-disable-bytecode-verification-in-a-production-system
QUICK_MAVEN_OPTS := "-XX:+TieredCompilation -XX:TieredStopAtLevel=1 -Xverify:none"

# - skip the tests
# - tell scoverage to skip: http://scoverage.github.io/scoverage-maven-plugin/1.4.0/report-mojo.html#skip
# - run up to 4 threads per core (4C): https://cwiki.apache.org/confluence/display/MAVEN/Parallel+builds+in+Maven+3
QUICK_MAVEN_ARGS := -DskipTests -Dscoverage.skip=true -T 4C

.PHONY: all apalache compile build-quick test integration clean deps

all: apalache

deps: $(DEPS)

apalache: deps
	# tell maven to load the binary libraries and build the package
	$(ENV) mvn package

# Just compile with quick settings
compile: $(DEPS)
	MAVEN_OPTS=$(QUICK_MAVEN_OPTS) mvn $(QUICK_MAVEN_ARGS) compile

# Build with quick settings, but and skip the tests
build-quick: $(DEPS)
	MAVEN_OPTS=$(QUICK_MAVEN_OPTS) mvn $(QUICK_MAVEN_ARGS) package

test:
	mvn test

integration: apalache
	# unit tests are run by mvn package
	# integration tests are run here
	cd test \
	 && $(ENV) ./run-integration

clean:
	mvn clean

$(DEPDIR)/lib:
	mkdir -p $(DEPDIR)/lib
	# install box by Jure (fix in the future!)
	cd "$(DEPDIR)" && ./install-local.sh

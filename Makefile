# a good old Makefile for the end users, as Maven is too much pain

ENV=NO_MVN=1

# See https://www.jrebel.com/blog/how-to-speed-up-your-maven-build
#
# - verify:none disables bytecode verification giving a speed boost, but should
#   not be used for releases or productin. See https://blogs.oracle.com/buck/never-disable-bytecode-verification-in-a-production-system
QUICK_MAVEN_OPTS := "-XX:+TieredCompilation -XX:TieredStopAtLevel=1 -Xverify:none"

# - skip the tests
# - tell scoverage to skip: http://scoverage.github.io/scoverage-maven-plugin/1.4.0/report-mojo.html#skip
# - run up to 4 threads per core (4C): https://cwiki.apache.org/confluence/display/MAVEN/Parallel+builds+in+Maven+3
QUICK_MAVEN_ARGS := -DskipTests -Dscoverage.skip=true -T 4C

# Markdown files used for integration tests
TEST_MD_FILES := $(wildcard test/tla/*.md)

.PHONY: all apalache apalache-jar compile build-quick test integration clean deps promote

all: apalache

apalache:
	# tell maven to load the binary libraries and build the package
	mvn package

apalache-jar:
	mvn --batch-mode --no-transfer-progress package -Dmaven.test.skip=true

# Just compile with quick settings
compile:
	MAVEN_OPTS=$(QUICK_MAVEN_OPTS) mvn $(QUICK_MAVEN_ARGS) compile

# Build with quick settings, but and skip the tests
build-quick:
	MAVEN_OPTS=$(QUICK_MAVEN_OPTS) mvn $(QUICK_MAVEN_ARGS) package

test:
	mvn test

integration:
	test/mdx-test.py --debug

# Invokes the md targets below
promote: $(TEST_MD_FILES)

# Copy corrected results over the incorrect expectations in the md files
test/tla/%.md: target/test/tla/%.md.corrected
	cp -f $< $@

fmt-check:
	git fetch origin
	mvn --batch-mode spotless:check || \
		( echo "TO FIX: run 'make fmt-fix' and commit the changes" ; \
		  exit 1 )

fmt-fix:
	mvn --batch-mode spotless:apply

clean:
	mvn clean
	rm -rf target/

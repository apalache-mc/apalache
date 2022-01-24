# a good old Makefile for the end users, so they don't need to learn SBT commands

# Markdown files used for integration tests
TEST_MD_FILES := $(wildcard test/tla/*.md)

.PHONY: all apalache apalache-jar compile build-quick test integration clean deps promote

all: apalache

# test and assemble the package
apalache:
	sbt test assembly

# package the project without running tests
package:
	sbt assembly

# compile, but don't assemble the package
compile:
	sbt compile

test:
	sbt test

# Run tests with scoverage report
test-coverage:
	sbt coverage test coverageAggregate

# run the integration tests
integration: package
	test/mdx-test.py --debug "$(TEST_FILTER)"

# build the docker image
docker:
	sbt docker

# Invokes the md targets below
promote: $(TEST_MD_FILES)

# Copy corrected results over the incorrect expectations in the md files
test/tla/%.md: target/test/tla/%.md.corrected
	cp -f $< $@

fmt-check:
	git fetch origin
	sbt scalafmtCheckAll scalafmtSbtCheck || \
		( echo "TO FIX: run 'make fmt-fix' and commit the changes" ; \
		  exit 1 )

fmt-fix:
	sbt scalafmtAll scalafmtSbt

clean:
	sbt clean
	rm -rf target/

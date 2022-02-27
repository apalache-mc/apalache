# a good old Makefile for the end users, so they don't need to learn SBT commands

# Markdown files used for integration tests
TEST_MD_FILES := $(wildcard test/tla/*.md)

.PHONY: all apalache apalache-jar compile build-quick test integration clean deps promote docker dist fmt-fix-unused

all: apalache

# test and assemble the package
apalache:
	sbt test apalacheCurrentPackage

# package the project for local use without running tests
package:
	sbt apalacheCurrentPackage

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

# Build the docker image
docker:
	sbt docker

# Create the distribution packages
# The archives without version suffix support stable links to the latest version.
# See https://github.com/informalsystems/apalache/issues/716
dist:
	sbt 'clean; Universal/packageZipTarball; Universal/packageBin; set Universal/packageName := "apalache"; Universal/packageZipTarball; Universal/packageBin'

# Invokes the md targets below
promote: $(TEST_MD_FILES)

# Copy corrected results over the incorrect expectations in the md files
test/tla/%.md: target/test/tla/%.md.corrected
	cp -f $< $@

fmt-check:
  # TODO: rm if we decide to keep running on all source files
	# git fetch origin
	sbt scalafmtCheckAll scalafmtSbtCheck scalafixEnable "scalafixAll --check RemoveUnused" || \
		( echo "TO FIX: run 'make fmt-fix' and commit the changes" ; \
		  exit 1 )

fmt-fix:
	sbt scalafixEnable "scalafixAll RemoveUnused" scalafmtAll scalafmtSbt

clean:
	sbt clean
	rm -rf target/

# Adapted from https://github.com/ocaml/dune/blob/d60cfbc0c78bb8733115d9100a8f7f6cb3dcf85b/Makefile#L121-L127
# If the first argument is "run"...
ifeq (run,$(firstword $(MAKECMDGOALS)))
  # use the rest as arguments for "run"
  RUN_ARGS := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  # ...and turn them into do-nothing targets
  $(eval $(RUN_ARGS):;@:)
endif

# Run apalache with the given `RUN_ARGS`, ensuring it has been built first
run:
	sbt "tool / run $(RUN_ARGS)"

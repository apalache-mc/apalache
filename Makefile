# A good old Makefile for the end users, so they don't need to learn SBT commands

# Markdown files used for integration tests
TEST_MD_FILES := $(wildcard test/tla/*.md)

.PHONY: default all apalache package compile test test-coverage integration docker dist fmt-check fmt-fix clean run docs docs-view quint-fixtures tla-io/src/test/resources/tictactoe.json test/tla/booleans.qnt.json

default: package

all: apalache

# Test and assemble the package for development and integration tests
#
# For packaging and distribution of releases, see the dist target
apalache:
	sbt test apalacheCurrentPackage

# Package the project for local development use without running tests
package:
	sbt apalacheCurrentPackage

# Compile, but don't assemble the package
compile:
	sbt compile

test:
	sbt test

# Compile code with fatal warnings enables
compile-strict: export APALACHE_FATAL_WARNINGS=true
compile-strict:
	sbt Test/compile compile

# Run tests with scoverage report
test-coverage:
	sbt coverage test coverageAggregate

# Run the integration tests
integration: package
	test/mdx-test.py --debug "$(TEST_FILTER)"

# Generate fixtures needed to test quint integration
quint-fixtures: tla-io/src/test/resources/tictactoe.json tla-io/src/test/resources/clockSync3.json test/tla/booleans.qnt.json

TEMP_QNT_TTT_FILE := $(shell mktemp)
tla-io/src/test/resources/tictactoe.json:
	curl https://raw.githubusercontent.com/informalsystems/quint/main/examples/puzzles/tictactoe/tictactoe.qnt > $(TEMP_QNT_TTT_FILE)
	quint typecheck --out $@ $(TEMP_QNT_TTT_FILE)
	rm $(TEMP_QNT_TTT_FILE)

TEMP_QNT_CS_FILE := $(shell mktemp)
tla-io/src/test/resources/clockSync3.json:
	curl https://raw.githubusercontent.com/informalsystems/quint/main/examples/classic/distributed/ClockSync/clockSync3.qnt > $(TEMP_QNT_TTT_FILE)
	quint typecheck --out $@ $(TEMP_QNT_CS_FILE)
	rm $(TEMP_QNT_CS_FILE)

TEMP_QNT_BOOL_FILE := $(shell mktemp)
test/tla/booleans.qnt.json:
	curl https://raw.githubusercontent.com/informalsystems/quint/main/examples/language-features/booleans.qnt > $(TEMP_QNT_BOOL_FILE)
	quint typecheck --out $@ $(TEMP_QNT_BOOL_FILE)
	rm $(TEMP_QNT_BOOL_FILE)

# Build the docker image
docker:
	sbt docker

# Create the distribution packages for releases and non-development usage
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
	sbt scalafmtCheckAll scalafmtSbtCheck scalafixEnable "scalafixAll --check RemoveUnused" || \
		( echo "TO FIX: run 'make fmt-fix' and commit the changes" ; \
		  exit 1 )

fmt-fix:
	sbt scalafixEnable "scalafixAll RemoveUnused" scalafmtAll scalafmtSbt

clean:
	sbt clean
	rm -rf target/

docs:
	sbt unidoc

docs-view:
	sbt "browseApiDocs; ~unidoc"

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

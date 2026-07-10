AENEAS_HOME := $(abspath aeneas)
JXL_RS_HOME := $(abspath jxl-rs)
CHARON := $(AENEAS_HOME)/charon/bin/charon
AENEAS := $(AENEAS_HOME)/bin/aeneas

.PHONY: prove
prove: aeneas | lean
	cd lean && lake build

# This recipe build a lake project with Aeneas (without extraction). The purpose is to use it when
# bumping the aeneas or jxl-rs commits, with the following process:
# - Remove the `lean` directory: `rm -rf lean`
# - Setup and build a lake project with Aeneas: `make`
# - Extract from JPEG XL: `make extract`
# - Manually merge and restore content (using `git status` and `git diff`)
# - Make sure the project builds before committing: `make`
lean:
	lake new jxl-proofs lib
	rm -rf jxl-proofs/.github
	printf '\n[[require]]\nname = "aeneas"\npath = "../aeneas/backends/lean"\n' \
	  >> jxl-proofs/lakefile.toml
	cp $(AENEAS_HOME)/backends/lean/lean-toolchain jxl-proofs
	mv jxl-proofs $@

.PHONY: extract
extract: aeneas jxl-rs
	$(CHARON) cargo --preset=aeneas --start-from="jxl::entropy_coding::ans::_::read" -- \
	  -p jxl --manifest-path $(JXL_RS_HOME)/Cargo.toml
	mv $(JXL_RS_HOME)/jxl.llbc .
	$(AENEAS) jxl.llbc -backend lean -split-files -dest lean -subdir JxlProofs

aeneas jxl-rs: %:
	$(error Missing $@ symlink. It must point to the root of the repository.)

.PHONY: test-commits
test-commits: aeneas jxl-rs
	@for i in $^; do \
	  echo -n "Checking $$i: "; \
	  if [ $$(cat $$i-commit) = $$(git -C $$i rev-parse HEAD) ]; then echo ok; \
	  else echo MISMATCH $$(git -C $$i rev-parse HEAD); fi; \
	done

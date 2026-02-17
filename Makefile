JXL_HOME ?= ../jxl-rs

all: prove

.PHONY: jxl.llbc
jxl.llbc:
	# FIXME: $(PWD) will not work if this Makefile is invoked with make -C 
	../charon/bin/charon cargo --preset=aeneas --start-from="jxl::entropy_coding::ans::_::read" -- -p jxl --manifest-path $(JXL_HOME)/Cargo.toml
	mv $(JXL_HOME)/$@ $@

extract: jxl.llbc
	../aeneas/bin/aeneas $< -backend lean -split-files -dest lean -subdir JxlProofs

prove: extract
	cd lean && lake build

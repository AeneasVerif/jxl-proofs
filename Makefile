JXL_HOME ?= ../jxl-rs

all: extract

.PHONY: jxl.llbc
jxl.llbc:
	# FIXME: $(PWD) will not work if this MAkefile is invoked with make -C 
	../charon/bin/charon cargo --preset=aeneas --start-from="jxl::entropy_coding::ans::_::read" -- -p jxl --manifest-path $(JXL_HOME)/Cargo.toml
	mv $(JXL_HOME)/$@ $@

extract: jxl.llbc
	cd lean && ../aeneas/bin/aeneas ../jxl.llbc -backend lean -split-files -subdir JxlProofs

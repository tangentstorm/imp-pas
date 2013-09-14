XPL = lib/xpl/code
GEN = gen
FPC = fpc -gl -B -Sgic -Fu$(XPL) -Fi$(GEN) -Fi$(XPL) -FE$(GEN)

targets:
	@echo 'available targets:'
	@echo '--------------------------'
	@echo 'make imp     -> build imp.pas as ./gen/imp'
	@echo 'make run     -> build and run ./gen/imp'
	@echo 'make raw     -> build ./gen/impraw (no prompt version)'
	@echo 'make test    -> build and test ./gen/impraw'
	@echo 'make unit    -> build and run unit tests'

imp: init imp.pas
	$(FPC) -dIMPSHELL imp.pas -oimp

run: imp
	$(GEN)/imp

raw: imp.pas
	$(FPC) -dIMPSHELL -dNOPROMPT -vn imp.pas -oimpraw

run-tests.pas:
	ln -F -s $(XPL)/../test/run-tests.pas

$(GEN)/imp.def: imp.pas
	python tools/impdefs.py  > imp.def

unit: $(GEN)/imp.def imp run-tests.pas
	@cd test; python ../$(XPL)/../test/gen-tests.py ../$(GEN)
	$(FPC) -Mobjfpc -vn run-tests.pas -Fu./test -oimptest
	$(GEN)/imptest

test: raw
	test/orgtest.py $(GEN)/impraw test/lisptests.org

roots: impraw
	test/orgtest.py $(GEN)/impraw test/roots.org

init: lib/xpl
	@mkdir -p $(GEN)

lib/xpl:
	@git submodule init
	@git submodule update

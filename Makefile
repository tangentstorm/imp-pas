XPL = lib/xpl/code
GEN = gen
FPC = fpc -gl -B -Sgic -Fu$(XPL) -Fi$(XPL) -FE$(GEN)

targets:
	@echo 'available targets:'
	@echo '--------------------------'
	@echo 'make imp     -> build implish.pas as ./gen/imp'
	@echo 'make run     -> build and run ./gen/imp'
	@echo 'make raw     -> build ./gen/impraw (no prompt version)'
	@echo 'make test    -> build and test ./gen/impraw'

imp: init imp.pas implish.pas
	$(FPC) implish.pas -oimp

run: imp
	$(GEN)/imp

raw:
	$(FPC) -dNOPROMPT -vn implish.pas -oimpraw

imptest:
	$(FPC) -vn imptest.pas
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

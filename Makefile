XPL = lib/xpl/code
GEN = gen
FPC = fpc -gl -B -Sgic -Fu$(XPL) -Fi$(XPL) -FE$(GEN)

targets:
	@echo 'available targets:'
	@echo '--------------------------'
	@echo 'make imp     -> build ./gen/imp'
	@echo 'make run     -> build and run ./gen/imp'
	@echo 'make imp     -> build ./gen/impraw (no prompt version)'
	@echo 'make test    -> build and test ./gen/impraw'

imp: init
	$(FPC) imp.pas

run: imp
	$(GEN)/imp

impraw:
	$(FPC) -dNOPROMPT -vn imp.pas -oimpraw

test: impraw
	test/orgtest.py $(GEN)/impraw test/lisptests.org
roots: impraw
	test/orgtest.py $(GEN)/impraw test/roots.org

init: lib/xpl
	@mkdir -p $(GEN)

lib/xpl:
	@git submodule init
	@git submodule update

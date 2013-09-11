XPL = lib/xpl/code
GEN = gen
FPC = fpc -gl -B -Sgic -Fu$(XPL) -Fi$(XPL) -FE$(GEN)

targets:
	@echo 'available targets:'
	@echo '--------------------------'
	@echo 'make imp     -> build ./gen/imp'
	@echo 'make run     -> build and run ./gen/imp'
	@echo 'make test    -> build and test ./gen/imp'

imp: init
	$(FPC) imp.pas

run: imp
	$(GEN)/imp

test: imp
	test/orgtest.py $(GEN)/imp test/lisptests.org

init: lib/xpl
	@mkdir -p $(GEN)

lib/xpl:
	@git submodule init
	@git submodule update

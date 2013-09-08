XPL = lib/xpl/code
GEN = gen
FPC = fpc -gl -B -Sgic -Fu$(XPL) -Fi$(XPL) -FE$(GEN)

targets:
	@echo 'available targets:'
	@echo '--------------------------'
	@echo 'make imp   -> build ./gen/imp'

imp: init
	$(FPC) imp.pas

init: lib/xpl
	@mkdir -p $(GEN)

lib/xpl:
	@git submodule init
	@git submodule update

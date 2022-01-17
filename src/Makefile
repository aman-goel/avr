REA_LOC = reach
DPA_LOC = dpa
VWN_LOC = vwn

all:
	make da
	make re
	make vw

clean:
	make dac
	make rec
	make vwc
	@echo Cleaning Complete

re:
	@cd $(REA_LOC); make
	@echo
	@echo %%% reach: Compilation Complete.

da:
	@cd $(DPA_LOC); make
	@echo
	@echo %%% dpa: Compilation Complete.

vw:
	@cd $(VWN_LOC) ; make
	@echo
	@echo %%% vwn: Compilation Complete.
	
rec:
	@cd $(REA_LOC); make clean

dac:
	@cd $(DPA_LOC); make clean

vwc:
	@cd $(VWN_LOC) ; make clean

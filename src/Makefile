#ENABLE_Y2 := 0
#ENABLE_M5 := 0
#ENABLE_BT := 0
#ENABLE_Z3 := 0

REA_LOC = reach
DPA_LOC = dpa
VWN_LOC = vwn

all:
	$(MAKE) vw
	$(MAKE) da
	ENABLE_Y2=1 $(MAKE) re
	ENABLE_BT=1 $(MAKE) re
#	ENABLE_M5=1 $(MAKE) re

clean:
	$(MAKE) vwc
	$(MAKE) dac
	$(MAKE) rec
	@echo Cleaning Complete

vw:
	@cd $(VWN_LOC) ; $(MAKE)
	@echo
	@echo %%% vwn: Compilation Complete.

da:
	@cd $(DPA_LOC); $(MAKE)
	@echo
	@echo %%% dpa: Compilation Complete.

re:
	@cd $(REA_LOC); $(MAKE)
	@echo
	@echo %%% reach: Compilation Complete.

vwc:
	@cd $(VWN_LOC) ; $(MAKE) clean

dac:
	@cd $(DPA_LOC); $(MAKE) clean

rec:
	@cd $(REA_LOC); $(MAKE) clean

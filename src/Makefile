REA_LOC = reach
DPA_LOC = dpa
VWN_LOC = vwn

all:
	$(MAKE) vw
	$(MAKE) da
	CONFIG_Y2BT=1 $(MAKE) re
	CONFIG_Y2=1 $(MAKE) re
	CONFIG_BT=1 $(MAKE) re

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

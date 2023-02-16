REA_LOC = reach
DPA_LOC = dpa
VWN_LOC = vwn

all:
	$(MAKE) da
	$(MAKE) re
	$(MAKE) vw

clean:
	$(MAKE) dac
	$(MAKE) rec
	$(MAKE) vwc
	@echo Cleaning Complete

re:
	@cd $(REA_LOC); $(MAKE)
	@echo
	@echo %%% reach: Compilation Complete.

da:
	@cd $(DPA_LOC); $(MAKE)
	@echo
	@echo %%% dpa: Compilation Complete.

vw:
	@cd $(VWN_LOC) ; $(MAKE)
	@echo
	@echo %%% vwn: Compilation Complete.

rec:
	@cd $(REA_LOC); $(MAKE) clean

dac:
	@cd $(DPA_LOC); $(MAKE) clean

vwc:
	@cd $(VWN_LOC) ; $(MAKE) clean

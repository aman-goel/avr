include ../makefile.include

HEADERS = *.h *.hpp
LINKTARGET = $(VWN_BIN)

INCLUDE  = -I.
LINKLIBS = 

ifeq ($(STATIC_VWN), 1)
  CXX += -static-libstdc++ -static-libgcc -static
  LINK_FLAGS += -L/usr/lib/x86_64-redhat-linux6E/lib64 
  LINK_FLAGS += -static -pthread -Wl,--whole-archive -lpthread -Wl,--no-whole-archive
  LINKLIBS += $(STATIC_GMPXX) $(STATIC_GMP)
else
  LINK_FLAGS += -pthread -lrt -ldl
  LINKLIBS +=  -lgmpxx -lgmp
endif

ifeq ($(ENABLE_VMT), 1)
  MSAT_DIR = $(DEPS)/mathsat
  MSAT_LIB = $(MSAT_DIR)/lib/libmathsat.a $(STATIC_GMPXX) $(STATIC_GMP)
  INCLUDE += -I$(MSAT_DIR)/include
  LINKLIBS += $(MSAT_LIB)
endif

ifeq ($(ENABLE_BTOR2), 1)
  BTOR2_DIR = $(DEPS)/btor2tools
  BTOR2_LIB = $(BTOR2_DIR)/build/lib/libbtor2parser.a
  INCLUDE += -I$(BTOR2_DIR)/src
  LINKLIBS += $(BTOR2_LIB)
endif


DEPDIR := .d
$(shell mkdir -p $(DEPDIR) >/dev/null)
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.Td

COMPILE.cc = $(CXX) $(DEPFLAGS) $(CFLAGS) $(INCLUDE)
POSTCOMPILE = mv -f $(DEPDIR)/$*.Td $(DEPDIR)/$*.d

all:
	make $(VWN_BIN)

$(VWN_BIN):$(VWN_OBJS)
	@mkdir -p $(@D)
	$(CXX) $(VWN_OBJS) $(LINK_FLAGS) $(LINKLIBS) -o $(VWN_BIN)

%.o : %.cpp
%.o : %.cpp $(DEPDIR)/%.d
	$(COMPILE.cc) $<
	$(POSTCOMPILE)

clean:
	rm -f *.o
	rm -f $(VWN_BIN)
	rm -rf .d/
	
$(DEPDIR)/%.d: ;
.PRECIOUS: $(DEPDIR)/%.d

-include $(patsubst %,$(DEPDIR)/%.d,$(basename $(VWN_OBJS)))

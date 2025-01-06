include ../makefile.include

CFLAGS += -fPIC -Wreturn-type -Wunknown-pragmas -Wunused-value -Wunused-label

ifeq ($(STATIC_REA), 1)
  CXX += -static-libstdc++ -static-libgcc -static
#  LINK_FLAGS += -L/usr/lib/x86_64-redhat-linux6E/lib64
  LINK_FLAGS += $(STATIC_GMPXX) $(STATIC_GMP) -pthread -Wl,--whole-archive -lpthread -Wl,--no-whole-archive
else
  LINK_FLAGS += -pthread -lgmpxx -lgmp -lrt -ldl
endif

ifeq ($(ENABLE_Y2), 1)
	Y2_DIR = $(DEPS)/yices2
	Y2_LIB = $(Y2_DIR)/build/x86_64-pc-linux-gnu-release/dist/lib/libyices.a  $(STATIC_GMPXX) $(STATIC_GMP)
	INCLUDE += -I$(Y2_DIR)/build/x86_64-pc-linux-gnu-release/dist/include
	LINKLIBS += $(Y2_LIB)
	CFLAGS += -D_Y2
endif
ifeq ($(CONFIG_Y2), 1)
  CFLAGS += -DBACKEND_Y2
  REACH_SUFFIX = y2
endif

ifeq ($(ENABLE_BT), 1)
	BT_DIR = $(DEPS)/boolector
	BT_LIB = $(BT_DIR)/build/lib/libboolector.a
	BT_LIB += $(BT_DIR)/deps/btor2tools/build/lib/libbtor2parser.a
	BT_LIB += $(BT_DIR)/deps/cadical/build/libcadical.a
	INCLUDE += -I$(BT_DIR)/src
	LINKLIBS += $(BT_LIB)
	CFLAGS += -D_BT
endif
ifeq ($(CONFIG_BT), 1)
  CFLAGS += -DBACKEND_BT
  REACH_SUFFIX = bt
endif

ifeq ($(ENABLE_M5), 1)
	MSAT_DIR = $(DEPS)/mathsat
	MSAT_LIB = $(MSAT_DIR)/lib/libmathsat.a $(STATIC_GMPXX) $(STATIC_GMP)
	INCLUDE += -I$(MSAT_DIR)/include
	LINKLIBS += $(MSAT_LIB)
	CFLAGS += -D_M5
endif
ifeq ($(CONFIG_M5), 1)
  CFLAGS += -DBACKEND_M5
  REACH_SUFFIX = m5
endif

ifeq ($(ENABLE_Z3), 1)
  Z3_DIR = $(DEPS)/z3
  Z3_LIB = $(Z3_DIR)/build/lib/libz3.a
  INCLUDE += -I$(Z3_DIR)/build/include
  LINKLIBS += $(Z3_LIB)
  CFLAGS += -D_Z3
endif

ifeq ($(CONFIG_Y2BT), 1)
  CFLAGS += -DBACKEND_Y2BT
  REACH_SUFFIX = y2bt
endif

DEPDIR := .d
$(shell mkdir -p $(DEPDIR) >/dev/null)
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.Td

COMPILE.cc = $(CXX) $(DEPFLAGS) $(CFLAGS) $(INCLUDE)
POSTCOMPILE = mv -f $(DEPDIR)/$*.Td $(DEPDIR)/$*.d

REACH_BIN = $(BIN_DIR)/reach_$(REACH_SUFFIX)

all:
	rm -f *.o
	$(MAKE) $(REACH_BIN)

$(REACH_BIN):$(REACH_OBJS)
	@mkdir -p $(@D)
	$(CXX) $(REACH_OBJS) $(LINK_FLAGS) $(LINKLIBS) -o $(REACH_BIN)

%.o : %.cpp
%.o : %.cpp $(DEPDIR)/%.d
	$(COMPILE.cc) $<
	$(POSTCOMPILE)

clean:
	rm -f *.o
	rm -f $(BIN_DIR)/reach*
	rm -rf .d/

$(DEPDIR)/%.d: ;
.PRECIOUS: $(DEPDIR)/%.d

-include $(patsubst %,$(DEPDIR)/%.d,$(basename $(REACH_OBJS)))

include ../makefile.include

CFLAGS += -Werror -Wreturn-type -Wunknown-pragmas -Wunused-value -Wunused-label

ifeq ($(STATIC_REA), 1)
  CXX += -static-libstdc++ -static-libgcc -static
  LINK_FLAGS += -L/usr/lib/x86_64-redhat-linux6E/lib64 
  LINK_FLAGS += $(STATIC_GMPXX) $(STATIC_GMP) -pthread -Wl,--whole-archive -lpthread -Wl,--no-whole-archive
else
  LINK_FLAGS += -pthread -lgmpxx -lgmp -lrt -ldl
endif

ifeq ($(ENABLE_Y2), 1)
  Y2_DIR = $(DEPS)/yices2
  Y2_LIB = $(Y2_DIR)/build/x86_64-pc-linux-gnu-release/dist/lib/libyices.a
  INCLUDE += -I$(Y2_DIR)/build/x86_64-pc-linux-gnu-release/dist/include
  LINKLIBS += $(Y2_LIB)
  CFLAGS += -D_Y2
endif

ifeq ($(ENABLE_Z3), 1)
  Z3_DIR = $(DEPS)/z3
  Z3_LIB = $(Z3_DIR)/build/lib/libz3.a
  INCLUDE += -I$(Z3_DIR)/build/include
  LINKLIBS += $(Z3_LIB)
  CFLAGS += -D_Z3
endif

ifeq ($(ENABLE_M5), 1)
  MSAT_DIR = $(DEPS)/mathsat
  MSAT_LIB = $(MSAT_DIR)/lib/libmathsat.a $(STATIC_GMPXX) $(STATIC_GMP)
  INCLUDE += -I$(MSAT_DIR)/include
  LINKLIBS += $(MSAT_LIB)
  CFLAGS += -D_M5
endif

ifeq ($(ENABLE_BT), 1)
  BT_DIR = $(DEPS)/boolector
  BT_LIB = $(BT_DIR)/build/lib/libboolector.a
  BT_LIB += $(BT_DIR)/deps/btor2tools/build/libbtor2parser.a
  BT_LIB += $(BT_DIR)/deps/cadical/build/libcadical.a
  INCLUDE += -I$(BT_DIR)/src
  LINKLIBS += $(BT_LIB)
  CFLAGS += -D_BT
endif

DEPDIR := .d
$(shell mkdir -p $(DEPDIR) >/dev/null)
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.Td

COMPILE.cc = $(CXX) $(DEPFLAGS) $(CFLAGS) $(INCLUDE)
POSTCOMPILE = mv -f $(DEPDIR)/$*.Td $(DEPDIR)/$*.d

all:
	make $(REACH_BIN)

$(REACH_BIN):$(REACH_OBJS)
	@mkdir -p $(@D)
	$(CXX) $(REACH_OBJS) $(LINK_FLAGS) $(LINKLIBS) -o $(REACH_BIN)

%.o : %.cpp
%.o : %.cpp $(DEPDIR)/%.d
	$(COMPILE.cc) $<
	$(POSTCOMPILE)

clean:
	rm -f *.o
	rm -f $(REACH_BIN)
	rm -rf .d/

$(DEPDIR)/%.d: ;
.PRECIOUS: $(DEPDIR)/%.d

-include $(patsubst %,$(DEPDIR)/%.d,$(basename $(REACH_OBJS)))

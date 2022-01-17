include ../makefile.include

ifeq ($(STATIC_DPA), 1)
  CXX += -static-libstdc++ -static-libgcc -static
  LINK_FLAGS += -L/usr/lib/x86_64-redhat-linux6E/lib64 
  LINK_FLAGS += $(STATIC_GMPXX) $(STATIC_GMP) -static -pthread -Wl,--whole-archive -lpthread -Wl,--no-whole-archive
else
  LINK_FLAGS += -pthread -lgmpxx -lgmp -lrt -ldl
endif

DEPDIR := .d
$(shell mkdir -p $(DEPDIR) >/dev/null)
DEPFLAGS = -MT $@ -MMD -MP -MF $(DEPDIR)/$*.Td

COMPILE.cc = $(CXX) $(DEPFLAGS) $(CFLAGS)
POSTCOMPILE = mv -f $(DEPDIR)/$*.Td $(DEPDIR)/$*.d

all:
	make $(DPA_BIN)

$(DPA_BIN):$(DPA_OBJS)
	@mkdir -p $(@D)
	$(CXX) $(DPA_OBJS) $(LINK_FLAGS) -o $(DPA_BIN)

%.o : %.cpp
%.o : %.cpp $(DEPDIR)/%.d
	$(COMPILE.cc) $<
	$(POSTCOMPILE)

clean:
	rm -f *.o
	rm -f $(DPA_BIN)
	rm -rf .d/

$(DEPDIR)/%.d: ;
.PRECIOUS: $(DEPDIR)/%.d

-include $(patsubst %,$(DEPDIR)/%.d,$(basename $(DPA_OBJS)))

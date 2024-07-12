
SRC_LIB = $(shell ls src/*.cpp src/parsing/*.cpp)
SRC_MAIN = main.cpp
SRC_TEST = $(shell ls test/*.cpp)
SYSTEM_LIB = $(shell ls lib/*.s)
VERSION = 1.0.0

CPPOPTS = -g

system: $(SRC_LIB:.cpp=.o) $(SRC_MAIN:.cpp=.o)
	g++ -o system $^

check: test_system $(SYSTEM_LIB)
	./test_system

test_system: $(SRC_LIB:.cpp=.o) $(SRC_TEST:.cpp=.o)
	g++ -o test_system -lgtest $^

ifneq ($(MAKECMDGOALS), clean)
ifneq ($(MAKECMDGOALS), distclean)
-include .config
-include $(SRC_LIB:.cpp=.d) main.d $(SRC_TEST:.cpp=.d)
endif
endif

install: system
	mkdir -p $(BINDIR)
	mkdir -p $(LIBDIR)
	cp lib/*.s $(LIBDIR)
	cp system $(BINDIR)

uninstall:
	rm -f $(BINDIR)/system
	rm -f $(subst lib/,$(LIBDIR)/,$(SYSTEM_LIB))
	rmdir --ignore-fail-on-non-empty $(LIBDIR)

.config:
	$(error Please run the configure script before running make)

%.d: %.cpp
	@echo g++ -MM $<
	@g++ -MM -MT '$*.o $*.d' -I src -I src/parsing $< > $@

%.o: %.cpp
	@echo g++ $(CPPOPTS) -o $@ -c $<
	@g++ $(CPPOPTS) -I src -I src/parsing -DLIBDIR=\"$(LIBDIR)\" -DVERSION=\"$(VERSION)\" \
		-o $@ -c $<

clean:
	rm -f src/*.o src/*.d src/parsing/*.o src/parsing/*.d test/*.o test/*.d
	rm -f *.o *.d test_system system

distclean: clean
	rm -f .config

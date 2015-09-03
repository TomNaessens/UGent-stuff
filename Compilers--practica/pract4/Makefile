LLVM_ROOT   = /opt/llvm-3.5
LLVM_CONFIG = $(LLVM_ROOT)/bin/llvm-config

CXXFLAGS    = $(shell $(LLVM_CONFIG) --cxxflags) -g -m32 -fno-rtti -Wall


#
# Main pass
#

BoundsCheck/libLLVMBoundsCheck.so: BoundsCheck/Pass.cpp
	$(CXX) $(CXXFLAGS) -shared $^ -o $@


#
# Testing
#

.PRECIOUS: test/%.ll

test/%.ll: test/%.c
	./cheetah -t bitcode -o $@ $<

test/%.checked.bc: test/%.ll BoundsCheck/libLLVMBoundsCheck.so
	$(LLVM_ROOT)/bin/opt -debug \
		-load BoundsCheck/libLLVMBoundsCheck.so -cheetah-boundscheck \
		-o $@ $<

test/%.ll: test/%.bc
	$(LLVM_ROOT)/bin/llvm-dis -o $@ $<

test/%.s: test/%.ll
	$(LLVM_ROOT)/bin/llc -march=x86 -o $@ $<

test/%.exe: test/%.s
	gcc -x assembler -m32 -o $@ $<


#
# Other
#

.PHONY: clean
clean:
	$(RM) BoundsCheck/libLLVMBoundsCheck.so
	$(RM) test/*.ll test/*.bc test/*.s test/*.exe

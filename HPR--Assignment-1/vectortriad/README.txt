Vector triad example code:

The files vectortriadGCC.cpp and vectortriadICC.cpp only differ in the way the compiler is informed about the memory alignment.

GCC (use version 4.7 or higher - available on Gengar)
=====================================================

* To compile:

module load GCC       (this will load latest version of GCC)
g++ -O3 vectortriadGCC.cpp -o vectortriad
./vectortriad

* To generate the assembly code (vectortriad.s):

g++ -O3 vectortriadGCC.cpp -S

* To enable the use of AVX instructions, add the flag "-march=corei7-avx" (Intel-based CPU) or "-march=btver2" (AMD-based CPU).  The generated binary might not run on your PC if your CPU does not support the AVX instructions.

Intel compiler (available on Gengar)
====================================

* To compile:

module load ictce
icc -O3 vectortriadICC.cpp -o vectortriad

* To generate the assembly code (vectortriad.s):

icc -O3 vectortriadICC.cpp -o vectortriad.s -S

To enable the use of AVX instructions, add the "-xAVX" flag.

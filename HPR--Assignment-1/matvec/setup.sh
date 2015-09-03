module load ictce/5.5.0
module load CMake/2.8.12-ictce-5.5.0
module load Valgrind
cmake .
make
./matvec > result.txt
./matvec256 > result256.txt
cat result.txt

# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 2.8

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list

# Produce verbose output by default.
VERBOSE = 1

# Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /vscmnt/gent_vulpix/_/apps/gent/SL6/sandybridge/software/CMake/2.8.12-ictce-5.5.0/bin/cmake

# The command to remove a file.
RM = /vscmnt/gent_vulpix/_/apps/gent/SL6/sandybridge/software/CMake/2.8.12-ictce-5.5.0/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The program to use to edit the cache.
CMAKE_EDIT_COMMAND = /vscmnt/gent_vulpix/_/apps/gent/SL6/sandybridge/software/CMake/2.8.12-ictce-5.5.0/bin/ccmake

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec

# Include any dependencies generated for this target.
include CMakeFiles/matvec.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/matvec.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/matvec.dir/flags.make

CMakeFiles/matvec.dir/matvec.cpp.o: CMakeFiles/matvec.dir/flags.make
CMakeFiles/matvec.dir/matvec.cpp.o: matvec.cpp
	$(CMAKE_COMMAND) -E cmake_progress_report /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec/CMakeFiles $(CMAKE_PROGRESS_1)
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Building CXX object CMakeFiles/matvec.dir/matvec.cpp.o"
	/usr/bin/c++   $(CXX_DEFINES) $(CXX_FLAGS) -o CMakeFiles/matvec.dir/matvec.cpp.o -c /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec/matvec.cpp

CMakeFiles/matvec.dir/matvec.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/matvec.dir/matvec.cpp.i"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_FLAGS) -E /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec/matvec.cpp > CMakeFiles/matvec.dir/matvec.cpp.i

CMakeFiles/matvec.dir/matvec.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/matvec.dir/matvec.cpp.s"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_FLAGS) -S /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec/matvec.cpp -o CMakeFiles/matvec.dir/matvec.cpp.s

CMakeFiles/matvec.dir/matvec.cpp.o.requires:
.PHONY : CMakeFiles/matvec.dir/matvec.cpp.o.requires

CMakeFiles/matvec.dir/matvec.cpp.o.provides: CMakeFiles/matvec.dir/matvec.cpp.o.requires
	$(MAKE) -f CMakeFiles/matvec.dir/build.make CMakeFiles/matvec.dir/matvec.cpp.o.provides.build
.PHONY : CMakeFiles/matvec.dir/matvec.cpp.o.provides

CMakeFiles/matvec.dir/matvec.cpp.o.provides.build: CMakeFiles/matvec.dir/matvec.cpp.o

# Object files for target matvec
matvec_OBJECTS = \
"CMakeFiles/matvec.dir/matvec.cpp.o"

# External object files for target matvec
matvec_EXTERNAL_OBJECTS =

matvec: CMakeFiles/matvec.dir/matvec.cpp.o
matvec: CMakeFiles/matvec.dir/build.make
matvec: /apps/gent/SL6/sandybridge/software/imkl/11.0.5.192/mkl/lib/intel64/libmkl_intel_lp64.so
matvec: /apps/gent/SL6/sandybridge/software/imkl/11.0.5.192/mkl/lib/intel64/libmkl_intel_thread.so
matvec: /apps/gent/SL6/sandybridge/software/imkl/11.0.5.192/mkl/lib/intel64/libmkl_core.so
matvec: /apps/gent/SL6/sandybridge/software/ifort/2013.5.192/compiler/lib/intel64/libiomp5.so
matvec: CMakeFiles/matvec.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --red --bold "Linking CXX executable matvec"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/matvec.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/matvec.dir/build: matvec
.PHONY : CMakeFiles/matvec.dir/build

CMakeFiles/matvec.dir/requires: CMakeFiles/matvec.dir/matvec.cpp.o.requires
.PHONY : CMakeFiles/matvec.dir/requires

CMakeFiles/matvec.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/matvec.dir/cmake_clean.cmake
.PHONY : CMakeFiles/matvec.dir/clean

CMakeFiles/matvec.dir/depend:
	cd /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec /user/home/gent/vsc408/vsc40889/HPR--Assignment-1/matvec/CMakeFiles/matvec.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/matvec.dir/depend

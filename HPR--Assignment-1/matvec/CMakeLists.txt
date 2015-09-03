# Project
project(matvec)

set(CMAKE_VERBOSE_MAKEFILE ON)

# Version Number
set(matvec_VERSION_MAJOR 1)
set(matvec_VERSION_MINOR 0)

# CMAKE version
cmake_minimum_required(VERSION 2.6)

# Enable fortran support
enable_language(Fortran)
find_package(BLAS REQUIRED)

# set the flags to -O2
set (CMAKE_CXX_FLAGS "-O2")

add_executable(matvec matvec.cpp)

target_link_libraries(matvec ${BLAS_LIBRARIES})

# Project
project(matmat)

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

add_executable(matmat matmat.cpp)
# add_executable(matmatSol matmatSol.cpp)

target_link_libraries(matmat ${BLAS_LIBRARIES})
# target_link_libraries(matmatSol ${BLAS_LIBRARIES})

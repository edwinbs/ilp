cmake_minimum_required(VERSION 2.6)

project(ilp)

set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}/bin")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_LIBRARY_OUTPUT_DIRECTORY}")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${PROJECT_BINARY_DIR}/bin")

add_definitions(-DSHOW_RESULTS)
add_definitions(-DSHOW_SYMBOLS)

find_package(DynamoRIO 3.1)
if (NOT DynamoRIO_FOUND)
  message(FATAL_ERROR "DynamoRIO package required to build")
endif(NOT DynamoRIO_FOUND)

add_library(ilp SHARED ilp.cc)
configure_DynamoRIO_client(ilp)


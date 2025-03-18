
CXXFLAGS:=-I../viper/include -I../viper_deps/concurrentqueue -I../viper/benchmark \
	-I../viper_deps/benchmark/include -I../viper_deps/libpmemobj-cpp/include -std=c++17 -mclwb \
	-DVIPER_BUILD_BENCHMARKS=ON -DCXX_COMPILATION -fPIC
LDFLAGS:=-lpmem -lpmemobj -lpmempool -lbenchmark 
CPP_FILE:=viper_wrapper.cpp
OBJ_FILE:=viper_wrapper.o
STATIC_LIB:=libviper_wrapper.a
SHARED_LIB:=viper_wrapper.so
CXX:=clang++

all:
	$(CXX) $(CPP_FILE) $(CXXFLAGS) $(LDFLAGS) 

obj: $(CPP_FILE)
	$(CXX) -c -o $(OBJ_FILE) $(CXXFLAGS)

static: $(OBJ_FILE)
	ar rcs $(STATIC_LIB) $(OBJ_FILE)

shared: $(OBJ_FILE)
	$(CXX) -shared -o $(SHARED_LIB) $(OBJ_FILE)

clean:
	@rm -rf $(STATIC_LIB) $(SHARED_LIB) $(OBJ_FILE) a.out
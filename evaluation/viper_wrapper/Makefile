# TODO: DONT HARDCODE
JAVA_HOME:=/usr/lib/jvm/java-17-openjdk-amd64

CXXFLAGS:=-I../viper/include -I../viper_deps/concurrentqueue -I../viper/benchmark \
	-I../viper_deps/benchmark/include -I../viper_deps/libpmemobj-cpp/include \
	-I$(JAVA_HOME)/include -I$(JAVA_HOME)/include/linux \
	-std=c++17 -mclwb -DCXX_COMPILATION -fPIC -DNDEBUG #-flto
LDFLAGS=-lpmem -lpmempool -lpmemobj -lbenchmark -pthread
SHARED_FLAGS=-L../viper_deps/benchmark/build/src -L/mnt/local_ssd/usr/lib/x86_64-linux-gnu/
WORKLOADX_FLAG=-DWORKLOADX
CPP_FILE=viper_wrapper.cpp
OBJ_FILE=viper_wrapper.o
OBJX_FILE=viper_wrapper_x.o
STATIC_LIB=libviper_wrapper.a
SHARED_LIB=libviper_wrapper.so
CXX=clang++
DEBUG=-g -O0 
OPTIMIZE=-O3

all: bin static shared

bin: $(CPP_FILE)
	$(CXX) $^ $(CXXFLAGS) $(LDFLAGS) $(OPTIMIZE)

obj_x: $(CPP_FILE)
	$(CXX) -c $^ -o $(OBJX_FILE) $(CXXFLAGS) $(WORKLOADX_FLAG) $(LDFLAGS)

# obj: $(CPP_FILE)
# 	$(CXX) -c $^ -o $(OBJ_FILE) $(CXXFLAGS) $(LDFLAGS)

static: $(OBJ_FILE)
	ar rcs $(STATIC_LIB) $(OPTIMIZE) $(OBJ_FILE)

static_big_val: $(OBJ_FILE)

# shared_x: $(OBJX_FILE) 
shared_x: $(CPP_FILE)
	$(CXX) -shared -o $(SHARED_LIB) $(OPTIMIZE) $(CXXFLAGS) $(SHARED_FLAGS) $(WORKLOADX_FLAG) $(LDFLAGS) $^  

shared: $(CPP_FILE)
	$(CXX) -shared -o $(SHARED_LIB) $(OPTIMIZE) $(CXXFLAGS) $(SHARED_FLAGS) $(LDFLAGS) $^  

clean:
	@rm -rf *.o *.so *a a.out
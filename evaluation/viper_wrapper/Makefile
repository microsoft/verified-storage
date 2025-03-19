# TODO: DONT HARDCODE
JAVA_HOME:=/usr/lib/jvm/java-17-openjdk-amd64

CXXFLAGS:=-I../viper/include -I../viper_deps/concurrentqueue -I../viper/benchmark \
	-I../viper_deps/benchmark/include -I../viper_deps/libpmemobj-cpp/include \
	-I$(JAVA_HOME)/include -I$(JAVA_HOME)/include/linux \
	-std=c++17 -mclwb -DCXX_COMPILATION -fPIC #-flto
LDFLAGS=-lpmem -lpmempool -lpmemobj -lbenchmark 
SHARED_FLAGS=-L../viper_deps/benchmark/build/src
CPP_FILE=viper_wrapper.cpp
# CPP_YCSB_WRAPPER=ycsb_wrapper.cpp
OBJ_FILE=viper_wrapper.o
# YCSB_OBJ_FILE:=ycsb_wrapper.o
STATIC_LIB=libviper_wrapper.a
SHARED_LIB=libviper_wrapper.so
CXX=clang++

all: bin static shared

bin: $(CPP_FILE)
	$(CXX) $^ $(CXXFLAGS) $(LDFLAGS) 

obj: $(CPP_FILE)
	$(CXX) -c $^ -o $(OBJ_FILE) $(CXXFLAGS) $(LDFLAGS)

# ycsb_obj: $(CPP_YCSB_WRAPPER)
# 	$(CXX) -c $^ -o $(YCSB_OBJ_FILE) $(CXXFLAGS) $(LDFLAGS)

static: $(OBJ_FILE)
	ar rcs $(STATIC_LIB) $(OBJ_FILE)

# shared: $(OBJ_FILE)
# 	$(CXX) -shared -o $(SHARED_LIB) $(OBJ_FILE)

# shared: $(CPP_FILE) $(CPP_YCSB_WRAPPER) 
shared: $(OBJ_FILE) 
	$(CXX) -shared -o $(SHARED_LIB) $(CXXFLAGS) $(SHARED_FLAGS) $(LDFLAGS) $^  

clean:
	@rm -rf *.o *.so *a a.out
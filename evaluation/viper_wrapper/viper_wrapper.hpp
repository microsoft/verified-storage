#ifndef VIPER_WRAPPER_HPP
#define VIPER_WRAPPER_HPP

#include <iostream>
#include "viper/viper.hpp"

// NOTE: if these are changed in the benchmark crate, they must also be changed here!
static const auto VIPER_KEY_LEN = 64;
static const auto VIPER_VALUE_LEN = 1024;

using K = uint64_t;
using V = uint64_t;
using ViperDB = viper::Viper<K, V>;
using ViperDBClient = viper::Viper<K, V>::Client;


extern "C" ViperDB* viperdb_create(
    const char* pool_file,
    uint64_t initial_pool_size
);

extern "C" ViperDBClient* viperdb_get_client(ViperDB* vdb);

extern "C" void viperdb_cleanup(ViperDB* vdb);

#endif
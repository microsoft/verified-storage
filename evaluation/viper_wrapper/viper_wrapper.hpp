#ifndef VIPER_WRAPPER_HPP
#define VIPER_WRAPPER_HPP

#include <iostream>
#include "viper/viper.hpp"
#include "benchmark.hpp"

// NOTE: if these are changed in the benchmark crate, they must also be changed here!
static const auto VIPER_KEY_LEN = 64;
static const auto VIPER_VALUE_LEN = 1024;

using K = viper::kv_bm::KeyType64;
using V = viper::kv_bm::ValueType1024;
using ViperDB = viper::Viper<K, V>;
using ViperDBClient = viper::Viper<K, V>::Client;

struct ViperDBFFI {
    std::unique_ptr<ViperDB> db;
    std::unique_ptr<ViperDBClient> client;
};

extern "C" struct ViperDBFFI* viperdb_create(const char* pool_file, uint64_t initial_pool_size);

extern "C" bool viperdb_put(struct ViperDBFFI* db, const K* key, const V* value);

extern "C" bool viperdb_get(struct ViperDBFFI* db, const K* key, V* value);

extern "C" bool viperdb_update(struct ViperDBFFI* db, const K* key, const V* value);

extern "C" bool viperdb_delete(struct ViperDBFFI* db, const K* key);

extern "C" void viperdb_cleanup(ViperDBFFI* db);

#endif
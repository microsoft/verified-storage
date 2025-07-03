#pragma once

#ifndef __VIPER_WRAPPER_HPP__
#define __VIPER_WRAPPER_HPP__

#include <iostream>
#include "viper/viper.hpp"
#include "benchmark.hpp"

using KeyType32 = viper::kv_bm::BMRecord<uint8_t, 32>;
using KeyType24 = viper::kv_bm::BMRecord<uint8_t, 24>;
using ValueType1140 = viper::kv_bm::BMRecord<uint8_t, 1140>;
using ValueType1050 = viper::kv_bm::BMRecord<uint8_t, 1050>;

// TODO: better way to select what key type to use
#ifdef CXX_COMPILATION
using K = KeyType24;
    #ifdef WORKLOADX
    using V = ValueType1050;
    #else
    using V = ValueType1140;
    #endif
#else
using K = viper::kv_bm::KeyType64;
using V = viper::kv_bm::ValueType1024;
#endif

using ViperDB = viper::Viper<K, V>;
using ViperDBClient = viper::Viper<K, V>::Client;

struct ViperDBFFI {
    ViperDB* db;
};

struct ViperDBClientFFI {
    ViperDBClient* client;
};

extern "C" struct ViperDBFFI* viperdb_create(const char* pool_file, uint64_t initial_pool_size);

extern "C" struct ViperDBClientFFI* viperdb_get_client(struct ViperDBFFI* db);

extern "C" bool viperdb_put(struct ViperDBClientFFI*, const K* key, const V* value);

extern "C" bool viperdb_get(struct ViperDBClientFFI*, const K* key, V* value);

extern "C" bool viperdb_update(struct ViperDBClientFFI*, const K* key, const V* value);

extern "C" bool viperdb_delete(struct ViperDBClientFFI*, const K* key);

extern "C" void viperdb_cleanup(ViperDBFFI* db);

extern "C" void viperdb_client_cleanup(ViperDBClientFFI* client);

#endif
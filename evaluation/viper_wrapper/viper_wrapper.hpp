#ifndef VIPER_WRAPPER_HPP
#define VIPER_WRAPPER_HPP

#include <iostream>
#include "viper/viper.hpp"

// NOTE: if these are changed in the benchmark crate, they must also be changed here!
static const auto VIPER_KEY_LEN = 64;
static const auto VIPER_VALUE_LEN = 1024;

using K = uint64_t;
using V = uint64_t;
using Viper = viper::Viper<K, V>;
using ViperDBClient = viper::Viper<K, V>::Client;

struct ViperDB {
    std::unique_ptr<Viper> db;
};

// struct ViperDBClient {
//     ViperDBClient::
// }

// class ViperDB {
//     public:
//         // ViperDB(std::unique_ptr<viper::Viper<unsigned char[VIPER_KEY_LEN], unsigned char[VIPER_VALUE_LEN]>>);
//         ViperDB(std::unique_ptr<Viper>);
//         ~ViperDB();

//         // ViperDB create(
//         //     const char* pool_file,
//         //     uint64_t initial_pool_size
//         // );

//         ViperDBClient get_client();

//     private:
//         // std::unique_ptr<viper::Viper<unsigned char[VIPER_KEY_LEN], unsigned char[VIPER_VALUE_LEN]>> db;
//         std::unique_ptr<Viper> db;
// };

extern "C" ViperDB* viperdb_create(
    const char* pool_file,
    uint64_t initial_pool_size
);

extern "C" ViperDBClient* viperdb_get_client(struct ViperDB* vdb);

// ViperDB::ViperDB(std::unique_ptr<Viper> viper_db) {
//     db = std::move(viper_db);
// }

// ViperDBClient ViperDB::get_client() {
//     return this->db->get_client();
// }

#endif
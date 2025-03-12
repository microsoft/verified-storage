#include "viper_wrapper.hpp"

using namespace std;

extern "C" ViperDB* viperdb_create(
    const char* pool_file,
    uint64_t initial_pool_size
) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string     
    auto viper_db = ViperDB::create(pool_file_string, initial_pool_size);
    auto db = viper_db.release();
    return db;
}

extern "C" ViperDBClient* viperdb_get_client(ViperDB* vdb) {
    auto client = vdb->get_client();
    return &client;
}

extern "C" void viperdb_cleanup(ViperDB* vdb) {
    delete vdb;
}
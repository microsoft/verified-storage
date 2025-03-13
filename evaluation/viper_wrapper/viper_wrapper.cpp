#include "viper_wrapper.hpp"

using namespace std;

extern "C" ViperDB* viperdb_create(
    const char* pool_file,
    uint64_t initial_pool_size
) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string     
    auto viper_db = ViperDB::create(pool_file_string, initial_pool_size);
    auto db = viper_db.release();
    printf("created db");
    return db;
}

extern "C" ViperDBClient* viperdb_get_client(ViperDB* vdb) {
    auto client = vdb->get_client();
    return &client;
}

extern "C" bool viperdb_put(ViperDBClient* db, const K* key, const V* value) {
    // return db->put(*key, *value);
    printf("%p\n", db);
    bool result = db->put(*key, *value);
    printf("put finished");
    return result;
}

extern "C" void viperdb_cleanup(ViperDB* vdb) {
    delete vdb;
}

// int main(void) {

//     const size_t initial_size = 1073741824;  // 1 GiB
//     auto file = "/mnt/pmem/viper";
//     auto db = viperdb_create(file, initial_size);
//     auto client = viperdb_get_client(db);

//     delete db;
// }
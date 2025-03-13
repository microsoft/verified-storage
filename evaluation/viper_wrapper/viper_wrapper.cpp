#include "viper_wrapper.hpp"

using namespace std;

extern "C" ViperDB* viperdb_create(
    const char* pool_file,
    uint64_t initial_pool_size
) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string     
    auto viper_db = ViperDB::create(pool_file_string, initial_pool_size);
    printf("map addr before release %p\n", &viper_db->map_);
    auto db = viper_db.release();
    printf("created db\n");
    printf("map addr after release %p\n", &db->map_);
    return db;
}

std::unique_ptr<ViperDB> viperdb_create_no_release(
    const char* pool_file,
    uint64_t initial_pool_size
) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string     
    auto viper_db = ViperDB::create(pool_file_string, initial_pool_size);
    // printf("map addr before release %p\n", &viper_db->map_);
    // auto db = viper_db.release();
    // printf("created db\n");
    // printf("map addr after release %p\n", &db->map_);
    return std::move(viper_db);
}

extern "C" ViperDBClient* viperdb_get_client(ViperDB* vdb) {
    printf("map addr before get client %p\n", &vdb->map_);
    auto client = vdb->get_client();
    printf("map addr after get client %p\n", &vdb->map_);
    printf("client map addr %p\n", &client.viper_.map_);
    return &client;
}

ViperDBClient viperdb_get_client_owned(ViperDB* vdb) {
    printf("map addr before get client %p\n", &vdb->map_);
    auto client = vdb->get_client();
    printf("map addr after get client %p\n", &vdb->map_);
    printf("client map addr %p\n", &client.viper_.map_);
    return client;
}

ViperDBClient* viperdb_get_client_from_unique_ptr(ViperDB* vdb) {
    printf("map addr before get client %p\n", &vdb->map_);
    auto client = vdb->get_client();
    // printf("map addr after get client %p\n", &vdb->map_);
    printf("client map addr %p\n", &client.viper_.map_);
    return &client;
}

extern "C" bool viperdb_put(ViperDBClient* db, const K* key, const V* value) {
    // return db->put(*key, *value);
    // printf("db addr %p\n", db);
    printf("map addr before put %p\n", &db->viper_.map_);
    bool result = db->put(*key, *value);
    printf("put finished\n");
    return result;
}

extern "C" void viperdb_cleanup(ViperDB* vdb) {
    delete vdb;
}

int main(void) {

    uint32_t val = 0;

    const size_t initial_size = 1073741824;  // 1 GiB
    auto file = "/mnt/pmem/viper";
    auto db = viperdb_create(file, initial_size);
    {
        // auto db = viperdb_create_no_release(file, initial_size);
        auto client = viperdb_get_client_owned(db);
        // auto client = viperdb_get_client_from_unique_ptr(db.get());

        // auto key = new viper::kv_bm::KeyType64(val);
        // auto value = new viper::kv_bm::ValueType1024(val);
        const K key = 0;
        const V value = 0;
        viperdb_put(&client, &key, &value);
    }
    
    // delete key;
    // delete value;

    delete db;

    printf("reached end of program\n");
}
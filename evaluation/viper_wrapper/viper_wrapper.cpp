#include "viper_wrapper.hpp"
#include <fcntl.h>
#include <sys/stat.h>

using namespace std;

extern "C" struct ViperDBFFI* viperdb_create(const char* pool_file, uint64_t initial_pool_size) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string   

    if (std::filesystem::exists(pool_file_string) && !std::filesystem::is_empty(pool_file_string)) {
        throw std::runtime_error("Cannot create new database in non-empty directory");
    }
    std::filesystem::create_directory(pool_file_string);

    viper::PMemAllocator::get().initialize();

    auto viper_db = ViperDB::create(pool_file_string, initial_pool_size);

    ViperDBFFI* db = new ViperDBFFI;

    auto client1 = viper_db->get_client();

    db->db = std::move(viper_db);

    auto client = std::make_unique<ViperDBClient>(client1);
    db->client = std::move(client);
    return db;
}

extern "C" bool viperdb_put(struct ViperDBFFI* db, const K* key, const V* value) {
    bool result = db->client->put(*key, *value);
    return result;
}

extern "C" bool viperdb_get(struct ViperDBFFI* db, const K* key, V* value) {
    return db->client->get(*key, value);
}

// NOTE: viper db puts are not atomic when updating an existing value
// TODO: figure out how to use their support for atomic updates
extern "C" bool viperdb_update(struct ViperDBFFI* db, const K* key, const V* value) {
    bool result = db->client->put(*key, *value);
    return result;
}

extern "C" bool viperdb_delete(struct ViperDBFFI* db, const K* key) {
    return db->client->remove(*key);
}

extern "C" void viperdb_cleanup(ViperDBFFI* db) {    
    delete db;
    viper::PMemAllocator::get().destroy();
}

#ifdef CXX_COMPILATION
int main(void) {
    uint32_t val = 0;

    const size_t initial_size = 1073741824;  // 1 GiB
    auto file = "/mnt/pmem/viper";

    {
        auto db = viperdb_create(file, initial_size);
        auto key = new viper::kv_bm::KeyType64(val);
        auto value = new viper::kv_bm::ValueType1024(val);
        viperdb_put(db, key, value);
        delete db;
    }

    std::filesystem::remove_all(file);

    {
        auto db = viperdb_create(file, initial_size);
        auto key = new viper::kv_bm::KeyType64(val);
        auto value = new viper::kv_bm::ValueType1024(val);
        viperdb_put(db, key, value);
        delete db;
    }
}
#endif
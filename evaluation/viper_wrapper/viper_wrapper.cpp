#include <fcntl.h>
#include <sys/stat.h>
#include "viper_wrapper.hpp"
#include "../YCSB/viper/target/headers/site_ycsb_db_Viper.h"

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

std::string jbytearray_to_string(JNIEnv* env, jbyteArray array) {
    // determine the needed length and allocate a buffer for it
    jsize num_bytes = env->GetArrayLength(array);
    // obtain the array elements
    jbyte* elements = env->GetByteArrayElements(array, NULL);

    std::string m(num_bytes, '\0');
    std::copy_n(elements, num_bytes, m.begin());

    env->ReleaseByteArrayElements(array, elements, 0);

    return m;
}

JNIEXPORT jlong JNICALL Java_site_ycsb_db_Viper_ViperCreate
        (JNIEnv * env, jclass _class, jbyteArray pool_file, jlong init_size) 
{
    std::string pool_file_str = jbytearray_to_string(env, pool_file);
    // copy the array elements into the buffer, and append a terminator

    auto db = viperdb_create(pool_file_str.c_str(), init_size);

    return (long)db;
}

JNIEXPORT jboolean JNICALL Java_site_ycsb_db_Viper_ViperPut
    (JNIEnv * env, jclass _class, jlong kv_ptr, jbyteArray key, jbyteArray value)
{
    struct ViperDBFFI* db = (struct ViperDBFFI*)kv_ptr;
    std::string key_string = jbytearray_to_string(env, key);
    std::string value_string = jbytearray_to_string(env, value);
    K viper_key = K();
    V viper_value = V();
    return viperdb_put(db, &viper_key.from_str(key_string), &viper_value.from_str(value_string));
}

JNIEXPORT jboolean JNICALL Java_site_ycsb_db_Viper_ViperUpdate
    (JNIEnv * env, jclass _class, jlong kv_ptr, jbyteArray key, jbyteArray value)
{
    return Java_site_ycsb_db_Viper_ViperPut(env, _class, kv_ptr, key, value);
}

JNIEXPORT jboolean JNICALL Java_site_ycsb_db_Viper_ViperRead
    (JNIEnv * env, jclass _class, jlong kv_ptr, jbyteArray key, jbyteArray value)
{
    struct ViperDBFFI* db = (struct ViperDBFFI*)kv_ptr;
    std::string key_string = jbytearray_to_string(env, key);
    K viper_key = K();
    V viper_value = V();
    bool result = viperdb_update(db, &viper_key.from_str(key_string), &viper_value);

    env->SetByteArrayRegion(value, 0, viper_value.data.size(), (jbyte*)viper_value.data.data());

    return result;
}

JNIEXPORT void JNICALL Java_site_ycsb_db_Viper_ViperCleanup
    (JNIEnv * _env, jclass _class, jlong kv_ptr) 
{
    struct ViperDBFFI* db = (struct ViperDBFFI*)kv_ptr;
    viperdb_cleanup(db);
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
#include <fcntl.h>
#include <sys/stat.h>
#include "viper_wrapper.hpp"
#include "../YCSB/viper/target/headers/site_ycsb_db_Viper.h"

using namespace std;

extern "C" struct ViperDBFFI* viperdb_create(const char* pool_file, uint64_t initial_pool_size) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string   

    std::unique_ptr<ViperDB> viper_db;

    if (std::filesystem::exists(pool_file_string) && !std::filesystem::is_empty(pool_file_string)) {
        // opening existing database instance
        viper::PMemAllocator::get().initialize();
        viper_db = ViperDB::open(pool_file_string);

    } else {
        // creating new database instance
        std::filesystem::create_directory(pool_file_string);

        viper::PMemAllocator::get().initialize();

        viper_db = ViperDB::create(pool_file_string, initial_pool_size);
    }

    ViperDBFFI* db = new ViperDBFFI;

    db->db = viper_db.release();

    return db;
    
}

extern "C" bool viperdb_put(struct ViperDBFFI* db, const K* key, const V* value) {
    auto client = db->db->get_client();
    bool result = client.put(*key, *value);
    return result;
}

extern "C" bool viperdb_get(struct ViperDBFFI* db, const K* key, V* value) {
    auto client = db->db->get_client();
    return client.get(*key, value);
}

// NOTE: viper db puts are not atomic when updating an existing value
// TODO: figure out how to use their support for atomic updates
extern "C" bool viperdb_update(struct ViperDBFFI* db, const K* key, const V* value) {
    auto client = db->db->get_client();
    bool result = client.put(*key, *value);
    return result;
}

extern "C" bool viperdb_delete(struct ViperDBFFI* db, const K* key) {
    auto client = db->db->get_client();
    return client.remove(*key);
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

    if (key_string.size() < viper_key.total_size) {
        // right pad the key with spaces to make it the correct size
        key_string.append(viper_key.total_size - key_string.size(), ' ');
    }

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
    uint64_t value_fill = 0;
    struct ViperDBFFI* db = (struct ViperDBFFI*)kv_ptr;
    std::string key_string = jbytearray_to_string(env, key);
    K viper_key = K();
    V viper_value = V(value_fill);
    if (key_string.size() < viper_key.total_size) {
        // right pad the key with spaces to make it the correct size
        key_string.append(viper_key.total_size - key_string.size(), ' ');
    }
    bool result = viperdb_get(db, &viper_key.from_str(key_string), &viper_value);

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
        // TODO: better way of handling different sizes of keys
        auto key = new K(val);
        auto value = new V(val);
        viperdb_put(db, key, value);
        delete db;
    }

    std::filesystem::remove_all(file);

    {
        auto db = viperdb_create(file, initial_size);
        auto key = new K(val);
        auto value = new V(val);
        viperdb_put(db, key, value);
        delete db;
    }
}
#endif
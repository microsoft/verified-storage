#include <fcntl.h>
#include <chrono>
#include <thread>
#include <sys/stat.h>
#include <unistd.h>
#include <pthread.h>
#include <stdio.h> 
#include <stdlib.h> 
#include "viper_wrapper.hpp"
#include "../YCSB/viper/target/headers/site_ycsb_db_Viper.h"
#include "../YCSB/viper/target/headers/site_ycsb_db_ViperThreadClient.h"

using namespace std;

extern "C" struct ViperDBFFI* viperdb_create(const char* pool_file, uint64_t initial_pool_size) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string   
    std::cout << initial_pool_size << " pool size" << std::endl;
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
    sync();

    ViperDBFFI* db = new ViperDBFFI;

    db->db = viper_db.release();

    return db;
}

extern "C" struct ViperDBClientFFI* viperdb_get_client(struct ViperDBFFI* db) {
    ViperDBClientFFI* client = new ViperDBClientFFI;
    client->client = db->db->get_client_unique_ptr().release();
    return client;
}

extern "C" bool viperdb_put(struct ViperDBClientFFI* client, const K* key, const V* value) {
    // the startup timing experiments intentionally fill up the KV store until we run out space.
    // viper handles this with an exception rather than returning an error code, so we have 
    // to handle that specially here.
    try {
        bool result = client->client->put(*key, *value);
        return result;
    } catch (const runtime_error& error) {
        return false;
    }
    
}

extern "C" bool viperdb_get(struct ViperDBClientFFI* client, const K* key, V* value) {
    return client->client->get(*key, value);
}

// NOTE: viper db puts are not atomic when updating an existing value
// TODO: figure out how to use their support for atomic updates
extern "C" bool viperdb_update(struct ViperDBClientFFI* client, const K* key, const V* value) {
    bool result = client->client->put(*key, *value);
    return result;
}

extern "C" bool viperdb_delete(struct ViperDBClientFFI* client, const K* key) {
    return client->client->remove(*key);
}

extern "C" void viperdb_cleanup(ViperDBFFI* db) { 
    delete db->db;
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    delete db;
    viper::PMemAllocator::get().destroy();
}

extern "C" void viperdb_client_cleanup(ViperDBClientFFI* client) {
    delete client->client;
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    delete client;
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

JNIEXPORT jlong JNICALL Java_site_ycsb_db_ViperThreadClient_ViperGetClient
  (JNIEnv * _env, jclass _class, jlong kv_ptr) 
{
    struct ViperDBFFI* db = (struct ViperDBFFI*)kv_ptr;
    return (long)viperdb_get_client(db);
}

JNIEXPORT jboolean JNICALL Java_site_ycsb_db_ViperThreadClient_ViperPut
    (JNIEnv * env, jclass _class, jlong client_ptr, jbyteArray key, jbyteArray value)
{
    struct ViperDBClientFFI* client = (struct ViperDBClientFFI*)client_ptr;
    std::string key_string = jbytearray_to_string(env, key);
    // std::cout << "key string: " << key_string << std::endl;
    std::string value_string = jbytearray_to_string(env, value);
    // std::cout << "value string: " << value_string << " " << value_string.size() << std::endl;
    K viper_key = K();
    V viper_value = V();

    if (key_string.size() < viper_key.total_size) {
        // right pad the key with spaces to make it the correct size
        key_string.append(viper_key.total_size - key_string.size(), ' ');
    }

    return viperdb_put(client, &viper_key.from_str(key_string), &viper_value.from_str(value_string));
}

JNIEXPORT jboolean JNICALL Java_site_ycsb_db_ViperThreadClient_ViperUpdate
    (JNIEnv * env, jclass _class, jlong client_ptr, jbyteArray key, jbyteArray value)
{
    return Java_site_ycsb_db_ViperThreadClient_ViperPut(env, _class, client_ptr, key, value);
}

JNIEXPORT jboolean JNICALL Java_site_ycsb_db_ViperThreadClient_ViperRead
    (JNIEnv * env, jclass _class, jlong client_ptr, jbyteArray key, jbyteArray value)
{
    uint64_t value_fill = 0;
    struct ViperDBClientFFI* client = (struct ViperDBClientFFI*)client_ptr;
    std::string key_string = jbytearray_to_string(env, key);
    K viper_key = K();
    V viper_value = V(value_fill);
    if (key_string.size() < viper_key.total_size) {
        // right pad the key with spaces to make it the correct size
        key_string.append(viper_key.total_size - key_string.size(), ' ');
    }
    bool result = viperdb_get(client, &viper_key.from_str(key_string), &viper_value);
    env->SetByteArrayRegion(value, 0, viper_value.data.size(), (jbyte*)viper_value.data.data());
    return result;
}

JNIEXPORT void JNICALL Java_site_ycsb_db_ViperThreadClient_ViperClientCleanup
    (JNIEnv * _env, jclass _class, jlong client_ptr)
{
    struct ViperDBClientFFI* client = (struct ViperDBClientFFI*)client_ptr;
    viperdb_client_cleanup(client);
}

JNIEXPORT void JNICALL Java_site_ycsb_db_Viper_ViperCleanup
    (JNIEnv * _env, jclass _class, jlong kv_ptr) 
{
    struct ViperDBFFI* db = (struct ViperDBFFI*)kv_ptr;
    viperdb_cleanup(db);
}

#ifdef CXX_COMPILATION
void magic_trace_stop_indicator() {}

struct workload_args {
    ViperDBFFI* db;
    uint32_t num_keys;
};

void* get_workload_for_trace(void* args) {
    uint32_t val = 0;
    int iterations = 10;
    struct workload_args* workload_args = (struct workload_args*)args;
    auto db = workload_args->db;
    auto num_keys = workload_args->num_keys;
    
    auto client = viperdb_get_client(db);
    auto value = new V(val);

    // also look at non-sequential?

    for (int j = 0; j < iterations; j++) {
        for (uint32_t i = 0; i < num_keys; i++) {
            auto key = new K(i);
            viperdb_get(client, key, value);
        }    
    }
    // magic_trace_stop_indicator();
    
    
    cout << "Cleaning up" << endl;
    viperdb_client_cleanup(client);
    
    return NULL;
}


const int NUM_THREADS = 16;
int main(void) {
    cout << "PID " << ::getpid() << std::endl;

    pthread_t tids[NUM_THREADS];

    uint64_t initial_size = 21474836480; 
    auto file = "/mnt/pmem/viper";
    uint32_t num_keys = 10000000;
    auto db = viperdb_create(file, initial_size);

    auto client = viperdb_get_client(db);
    uint32_t val = 0;
    auto value = new V(val);

    cout << "Filling in the KV store" << endl;
    // fill in the kv store
    for (uint32_t i = 0; i < num_keys; i++) {
        auto key = new K(i);
        viperdb_put(client, key, value);
    }

    viperdb_client_cleanup(client);

    struct workload_args args{db, num_keys};

    cout << "Done, starting reader threads" << endl;
    for (int i = 0; i < NUM_THREADS; i++) {
        // get_workload_for_trace(db);
        pthread_create(&tids[i], NULL, get_workload_for_trace, (void*)&args);
    }

    get_workload_for_trace(&args);

    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(tids[i], NULL);
    }

    viperdb_cleanup(db);

    // uint32_t val = 0;

    // {
    //     auto db = viperdb_create(file, initial_size);
    //     auto client = viperdb_get_client(db);
    //     // TODO: better way of handling different sizes of keys
    //     auto key = new K(val);
    //     auto value = new V(val);
    //     viperdb_put(client, key, value);
        
    //     viperdb_client_cleanup(client);
    //     viperdb_cleanup(db);
    // }

    // std::filesystem::remove_all(file);

    // {
    //     auto db = viperdb_create(file, initial_size);
    //     auto client = viperdb_get_client(db);
    //     auto key = new K(val);
    //     auto value = new V(val);
    //     viperdb_put(client, key, value);

    //     viperdb_client_cleanup(client);
    //     viperdb_cleanup(db);
    // }
}
#endif
#include "viper_wrapper.hpp"
#include "../YCSB/viper/target/headers/site_ycsb_db_Viper.h"

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
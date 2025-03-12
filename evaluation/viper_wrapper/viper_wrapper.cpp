#include "viper_wrapper.hpp"

using namespace std;

extern "C" ViperDB* viperdb_create(
    const char* pool_file,
    uint64_t initial_pool_size
) {
    std::string pool_file_string = pool_file; // convert Rust-compatible string to a C++ string 
    cout << "viperdb pool file: " << pool_file_string << endl;
    
    auto viper_db = Viper::create(pool_file_string, initial_pool_size);
    auto db = ViperDB {
        viper_db.release()
    };
    return &db;
}

extern "C" ViperDBClient* viperdb_get_client(struct ViperDB* vdb) {
    auto client = vdb->db->get_client();
    return &client;
}

extern "C" void viperdb_cleanup(struct ViperDB* vdb) {
    delete vdb->db;
}
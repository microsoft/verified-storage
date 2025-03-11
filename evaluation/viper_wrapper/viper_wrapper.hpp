#include <iostream>

#include "viper/viper.hpp"

// NOTE: if these are changed in the benchmark crate, they must also be changed here!
static const auto VIPER_KEY_LEN = 64;
static const auto VIPER_VALUE_LEN = 1024;

class ViperDB {
    public:
        // ViperDB(std::unique_ptr<viper::Viper<unsigned char[VIPER_KEY_LEN], unsigned char[VIPER_VALUE_LEN]>>);
        ViperDB(std::unique_ptr<viper::Viper<uint64_t, uint64_t>>);
        ~ViperDB();

    private:
        // std::unique_ptr<viper::Viper<unsigned char[VIPER_KEY_LEN], unsigned char[VIPER_VALUE_LEN]>> db;
        std::unique_ptr<viper::Viper<uint64_t, uint64_t>> db;
};

static ViperDB create(
    const std::string& pool_file, 
    uint64_t initial_pool_size
) {
    // auto viper_db = viper::Viper<unsigned char[VIPER_KEY_LEN], unsigned char[VIPER_VALUE_LEN]>::create(pool_file, initial_pool_size);
    auto viper_db = viper::Viper<uint64_t, uint64_t>::create(pool_file, initial_pool_size);

    return ViperDB(std::move(viper_db));
}
#include <atomic>
#include <stdlib.h>
#include <stdint.h>
#include <iostream>
#include <thread>
#include <vector>
#include <chrono>
#include <mutex>

using namespace std;

atomic<uint64_t> sema = 0;
const int iters = 1000000;
mutex timing_lock;
vector<uint64_t> timing;


void sema_cas(void) {
    for (int i = 0; i < iters; i++) {
        chrono::steady_clock::time_point begin = chrono::steady_clock::now();
        auto v = sema.load();
        sema.compare_exchange_weak(v, v+1);
        sema.fetch_sub(1);
        chrono::steady_clock::time_point end = chrono::steady_clock::now();
        auto time = std::chrono::duration_cast<std::chrono::nanoseconds>(end - begin).count();
        timing_lock.lock();
        timing.push_back(time);
        timing_lock.unlock();
    }
}

void run_benchmark(int num_threads) {
    vector<thread> threads;

    for (int i = 0; i < num_threads; i++) {
        thread t(sema_cas); 
        threads.push_back(move(t));
    }

    for (int i = 0; i < num_threads; i++) {
        threads[i].join();
    }

    uint64_t sum = 0;
    for (int i = 0; i < timing.size(); i++) {
        sum += timing[i];
    }
    cout << "average time " << num_threads << " threads: " << sum / timing.size() << endl;
}

int main(void) {
    run_benchmark(1);
    run_benchmark(2);
    run_benchmark(4);
    run_benchmark(8);
    run_benchmark(16);
}
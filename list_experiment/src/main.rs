#![allow(unused_imports)]
use crate::block_list::*;
use crate::list::*;
use crate::mem_pool::*;
use crate::mock_pool::*;
use crate::singleton_list::*;
use crate::table::*;
use std::time::Instant;

mod block_list;
mod err;
mod list;
mod mem_pool;
mod mock_pool;
mod singleton_list;
mod table;
mod test;

const CDB_FALSE: u64 = 0xa32842d19001605e; // CRC(b"0")
const CDB_TRUE: u64 = 0xab21aa73069531b7; // CRC(b"1")

const MEM_POOL_SIZE: usize = 1024 * 1024 * 1024;
const LIST_LEN: u64 = 50000;
const ITERATIONS: u64 = 5;

fn main() {
    append_experiments();
    read_experiments();
    trim_experiments();
}

fn append_experiments() {
    singleton_append_experiments();
    block_append_experiments();
}

fn read_experiments() {
    singleton_read_experiments();
    block_read_experiments();
}

fn trim_experiments() {
    singleton_trim_experiments();
    block_trim_experiments();
}

fn singleton_append_experiments() {
    println!("singleton append,");
    println!("element size,ms elapsed,");

    run_singleton_append_experiment::<8>();
    run_singleton_append_experiment::<16>();
    run_singleton_append_experiment::<32>();
    run_singleton_append_experiment::<64>();
    run_singleton_append_experiment::<128>();
    run_singleton_append_experiment::<256>();
    run_singleton_append_experiment::<512>();
    run_singleton_append_experiment::<1024>();

    println!("");
}

fn singleton_read_experiments() {
    println!("singleton read,");
    println!("element size,ms elapsed,");

    run_singleton_read_experiment::<8>();
    run_singleton_read_experiment::<16>();
    run_singleton_read_experiment::<32>();
    run_singleton_read_experiment::<64>();
    run_singleton_read_experiment::<128>();
    run_singleton_read_experiment::<256>();
    run_singleton_read_experiment::<512>();
    run_singleton_read_experiment::<1024>();

    println!("");
}

fn singleton_trim_experiments() {
    println!("singleton trim,");
    println!("element size,trim_size,ms elapsed,");

    let trim_len = 1;
    run_singleton_trim_experiment::<8>(trim_len);
    run_singleton_trim_experiment::<16>(trim_len);
    run_singleton_trim_experiment::<32>(trim_len);
    run_singleton_trim_experiment::<64>(trim_len);
    run_singleton_trim_experiment::<128>(trim_len);
    run_singleton_trim_experiment::<256>(trim_len);
    run_singleton_trim_experiment::<512>(trim_len);
    run_singleton_trim_experiment::<1024>(trim_len);

    println!("");
}

fn block_append_experiments() {
    println!("block append,");
    println!("element size,block_size,ms elapsed,");

    run_block_append_experiment::<8, 8>();
    run_block_append_experiment::<16, 8>();
    run_block_append_experiment::<32, 8>();
    run_block_append_experiment::<64, 8>();
    run_block_append_experiment::<128, 8>();
    run_block_append_experiment::<256, 8>();
    run_block_append_experiment::<512, 8>();
    run_block_append_experiment::<1024, 8>();

    println!("");

    run_block_append_experiment::<8, 2>();
    run_block_append_experiment::<16, 2>();
    run_block_append_experiment::<32, 2>();
    run_block_append_experiment::<64, 2>();
    run_block_append_experiment::<128, 2>();
    run_block_append_experiment::<256, 2>();
    run_block_append_experiment::<512, 2>();
    run_block_append_experiment::<1024, 2>();

    println!("");

    run_block_append_experiment::<8, 16>();
    run_block_append_experiment::<16, 16>();
    run_block_append_experiment::<32, 16>();
    run_block_append_experiment::<64, 16>();
    run_block_append_experiment::<128, 16>();
    run_block_append_experiment::<256, 16>();
    run_block_append_experiment::<512, 16>();
    run_block_append_experiment::<1024, 16>();

    println!("");
}

fn block_read_experiments() {
    println!("block read,");
    println!("element size,block_size,ms elapsed,");

    run_block_read_experiment::<8, 8>();
    run_block_read_experiment::<16, 8>();
    run_block_read_experiment::<32, 8>();
    run_block_read_experiment::<64, 8>();
    run_block_read_experiment::<128, 8>();
    run_block_read_experiment::<256, 8>();
    run_block_read_experiment::<512, 8>();
    run_block_read_experiment::<1024, 8>();

    println!("");

    run_block_read_experiment::<8, 2>();
    run_block_read_experiment::<16, 2>();
    run_block_read_experiment::<32, 2>();
    run_block_read_experiment::<64, 2>();
    run_block_read_experiment::<128, 2>();
    run_block_read_experiment::<256, 2>();
    run_block_read_experiment::<512, 2>();
    run_block_read_experiment::<1024, 2>();

    println!("");

    run_block_read_experiment::<8, 16>();
    run_block_read_experiment::<16, 16>();
    run_block_read_experiment::<32, 16>();
    run_block_read_experiment::<64, 16>();
    run_block_read_experiment::<128, 16>();
    run_block_read_experiment::<256, 16>();
    run_block_read_experiment::<512, 16>();
    run_block_read_experiment::<1024, 16>();

    println!("");
}

fn block_trim_experiments() {
    println!("block trim,");
    println!("element size,block_size,trim_size,ms elapsed,");

    let trim_len = 1;
    run_block_trim_experiment::<8, 8>(trim_len);
    run_block_trim_experiment::<16, 8>(trim_len);
    run_block_trim_experiment::<32, 8>(trim_len);
    run_block_trim_experiment::<64, 8>(trim_len);
    run_block_trim_experiment::<128, 8>(trim_len);
    run_block_trim_experiment::<256, 8>(trim_len);
    run_block_trim_experiment::<512, 8>(trim_len);
    run_block_trim_experiment::<1024, 8>(trim_len);

    println!("");

    run_block_trim_experiment::<8, 2>(trim_len);
    run_block_trim_experiment::<16, 2>(trim_len);
    run_block_trim_experiment::<32, 2>(trim_len);
    run_block_trim_experiment::<64, 2>(trim_len);
    run_block_trim_experiment::<128, 2>(trim_len);
    run_block_trim_experiment::<256, 2>(trim_len);
    run_block_trim_experiment::<512, 2>(trim_len);
    run_block_trim_experiment::<1024, 2>(trim_len);

    println!("");

    run_block_trim_experiment::<8, 16>(trim_len);
    run_block_trim_experiment::<16, 16>(trim_len);
    run_block_trim_experiment::<32, 16>(trim_len);
    run_block_trim_experiment::<64, 16>(trim_len);
    run_block_trim_experiment::<128, 16>(trim_len);
    run_block_trim_experiment::<256, 16>(trim_len);
    run_block_trim_experiment::<512, 16>(trim_len);
    run_block_trim_experiment::<1024, 16>(trim_len);

    println!("");
}

fn avg_duration(times: Vec<u128>) -> u128 {
    let mut sum = 0;
    for t in &times {
        sum += t;
    }
    let vec_len: u128 = times.len().try_into().unwrap();
    sum / vec_len
}

fn run_singleton_append_experiment<const N: usize>() {
    let mut times: Vec<u128> = Vec::new();
    for _ in 0..ITERATIONS {
        let mut mock_pool = MockPool::new(MEM_POOL_SIZE);
        let mut table: SingletonListTable<N> = SingletonListTable::new(0, mock_pool.len());
        let mut list: DurableSingletonList<N> = DurableSingletonList::new();

        let value = [0; N];

        let start = Instant::now();
        for _ in 0..LIST_LEN {
            list.append(&mut mock_pool, &mut table, &value).unwrap();
        }
        let elapsed = start.elapsed();
        // let elements_per_ms = LIST_LEN as u128 / elapsed.as_millis();
        // let kb_appended: u128 = ((N * LIST_LEN as usize) / 1024).try_into().unwrap();
        // let kb_per_ms = kb_appended / elapsed.as_millis();

        // println!(
        //     "append singleton list with {:?}B elements: {:?}us, {:?} appends/ms, {:?} kb/ms",
        //     N,
        //     elapsed.as_millis(),
        //     elements_per_ms,
        //     kb_per_ms,
        // );
        times.push(elapsed.as_millis());
    }
    println!("{:?},{:?},", N, avg_duration(times));
}

fn run_singleton_read_experiment<const N: usize>() {
    let mut times: Vec<u128> = Vec::new();
    for _ in 0..ITERATIONS {
        let mut mock_pool = MockPool::new(MEM_POOL_SIZE);
        let mut table: SingletonListTable<N> = SingletonListTable::new(0, mock_pool.len());
        let mut list: DurableSingletonList<N> = DurableSingletonList::new();

        let value = [0; N];

        for _ in 0..LIST_LEN {
            list.append(&mut mock_pool, &mut table, &value).unwrap();
        }

        let start = Instant::now();
        let _vec = list.read_full_list(&mock_pool, &table).unwrap();
        let elapsed = start.elapsed();
        // let kb_read: u128 = ((N * LIST_LEN as usize) / 1024).try_into().unwrap();
        // let kb_per_ms = kb_read / elapsed.as_millis();

        // println!(
        //     "read singleton list with {:?}B elements: {:?}us, {:?} kb/ms",
        //     N,
        //     elapsed.as_millis(),
        //     kb_per_ms,
        // );
        times.push(elapsed.as_millis());
    }
    println!("{:?},{:?},", N, avg_duration(times));
}

fn run_singleton_trim_experiment<const N: usize>(trim_len: u64) {
    let mut times = Vec::new();
    for _ in 0..ITERATIONS {
        let mut mock_pool = MockPool::new(MEM_POOL_SIZE);
        let mut table: SingletonListTable<N> = SingletonListTable::new(0, mock_pool.len());
        let mut list: DurableSingletonList<N> = DurableSingletonList::new();

        let value = [0; N];

        for _ in 0..LIST_LEN {
            list.append(&mut mock_pool, &mut table, &value).unwrap();
        }

        let start = Instant::now();
        for _ in 0..LIST_LEN {
            list.trim(&mut mock_pool, &mut table, trim_len).unwrap();
        }
        let elapsed = start.elapsed();

        // println!(
        //     "trim singleton list with {:?}B elements, {:?} trim_len: {:?}us",
        //     N,
        //     trim_len,
        //     elapsed.as_millis(),
        // );
        times.push(elapsed.as_millis());
    }
    println!("{:?},{:?},{:?},", N, trim_len, avg_duration(times));
}

fn run_block_append_experiment<const N: usize, const M: usize>() {
    let mut times = Vec::new();
    for _ in 0..ITERATIONS {
        let mut mock_pool = MockPool::new(MEM_POOL_SIZE);
        let mut table: BlockListTable<N, M> = BlockListTable::new(0, mock_pool.len());
        let mut list: DurableBlockList<N, M> = DurableBlockList::new();

        let value = [0; N];

        let start = Instant::now();
        for _ in 0..LIST_LEN {
            list.append(&mut mock_pool, &mut table, &value).unwrap();
        }
        let elapsed = start.elapsed();
        // let elements_per_ms = LIST_LEN as u128 / elapsed.as_millis();
        // let kb_appended: u128 = ((N * LIST_LEN as usize) / 1024).try_into().unwrap();
        // let kb_per_ms = kb_appended / elapsed.as_millis();

        // println!(
        //     "append block list with {:?}B elements, {:?} rows per node: {:?}us, {:?} appends/ms, {:?} kb/ms",
        //     N,
        //     M,
        //     elapsed.as_millis(),
        //     elements_per_ms,
        //     kb_per_ms,
        // );
        times.push(elapsed.as_millis());
    }
    println!("{:?},{:?},{:?},", N, M, avg_duration(times));
}

fn run_block_read_experiment<const N: usize, const M: usize>() {
    let mut times = Vec::new();
    for _ in 0..ITERATIONS {
        let mut mock_pool = MockPool::new(MEM_POOL_SIZE);
        let mut table: BlockListTable<N, M> = BlockListTable::new(0, mock_pool.len());
        let mut list: DurableBlockList<N, M> = DurableBlockList::new();

        let value = [0; N];

        for _ in 0..LIST_LEN {
            list.append(&mut mock_pool, &mut table, &value).unwrap();
        }

        let start = Instant::now();
        let _vec = list.read_full_list(&mock_pool, &table).unwrap();
        let elapsed = start.elapsed();
        // let kb_read: u128 = ((N * LIST_LEN as usize) / 1024).try_into().unwrap();
        // let kb_per_ms = kb_read / elapsed.as_millis();

        // println!(
        //     "read block list with {:?}B elements, {:?} rows per node: {:?}us, {:?} kb/ms",
        //     N,
        //     M,
        //     elapsed.as_millis(),
        //     kb_per_ms,
        // );

        times.push(elapsed.as_millis());
    }
    println!("{:?},{:?},{:?},", N, M, avg_duration(times));
}

fn run_block_trim_experiment<const N: usize, const M: usize>(trim_len: u64) {
    let mut times = Vec::new();
    for _ in 0..ITERATIONS {
        let mut mock_pool = MockPool::new(MEM_POOL_SIZE);
        let mut table: BlockListTable<N, M> = BlockListTable::new(0, mock_pool.len());
        let mut list: DurableBlockList<N, M> = DurableBlockList::new();

        let value = [0; N];

        for _ in 0..LIST_LEN {
            list.append(&mut mock_pool, &mut table, &value).unwrap();
        }

        let start = Instant::now();
        for _ in 0..LIST_LEN {
            list.trim(&mut mock_pool, &mut table, trim_len).unwrap();
        }
        let elapsed = start.elapsed();

        // println!(
        //     "trim block list with {:?}B elements, {:?} rows per node, {:?} trim size: {:?}us",
        //     N,
        //     M,
        //     trim_len,
        //     elapsed.as_millis(),
        // );
        times.push(elapsed.as_millis());
    }
    println!("{:?},{:?},{:?},{:?},", N, M, trim_len, avg_duration(times));
}

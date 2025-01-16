use crate::list::*;
use crate::table::*;

pub struct DurableSingletonListNode<const N: usize> {
    val: [u8; N],
    crc: u64,
    next: u64,
}

pub struct VolatileSingletonListNode<const N: usize> {
    val: [u8; N],
    next: Option<Box<VolatileSingletonListNode<N>>>,
}

impl<const N: usize> VolatileListNode for VolatileSingletonListNode<N> {
    fn next(&self) -> Option<&Self> {
        match &self.next {
            None => None,
            Some(node) => Some(&node),
        }
    }
}

// this doesn't make any sense. volatile list nodes are for reading, not writing.
// just need an append function to write a given value to the list
// pub fn build_volatile_singleton_list_with_len<const N: usize>(
//     len: u64,
// ) -> Option<VolatileSingletonListNode<N>> {
//     if len == 0 {
//         None
//     } else {
//         // create what will be the tail of the list
//         let mut bytes = [0; N];
//         let val = len.to_ne_bytes();
//         bytes[0..8].copy_from_slice(&val);
//         let mut current = VolatileSingletonListNode {
//             val: bytes,
//             next: None,
//         };

//         // build the list backwards (just because it seems a little easier ownership-wise)
//         for i in 1..len {
//             let mut bytes = [0; N];
//             let val = i.to_ne_bytes();
//             bytes[0..8].copy_from_slice(&val);
//             let new = VolatileSingletonListNode {
//                 val: bytes,
//                 next: Some(Box::new(current)),
//             };
//             current = new;
//         }
//         // return the head of the list
//         Some(current)
//     }
// }

pub struct SingletonListTable<const N: usize> {
    metadata: TableMetadata,
    free_list: Vec<u64>,
}

impl<const N: usize> ListTable for SingletonListTable<N> {
    // Creates a free list and metadata structure for a table to store
    // singleton list nodes. Determines how many rows the table can have
    // based on provided total table size in bytes `mem_size`.
    fn new(mem_start: u64, mem_size: u64) -> Self {
        let row_size = std::mem::size_of::<DurableSingletonListNode<N>>()
            .try_into()
            .unwrap();
        let num_rows = mem_size / row_size;

        let metadata = TableMetadata::new(mem_start, num_rows, row_size);
        let mut free_list = Vec::with_capacity(num_rows as usize);
        for i in 1..num_rows {
            free_list.push(metadata.row_index_to_addr(i));
        }

        Self {
            metadata,
            free_list,
        }
    }

    // This function allocates and returns a free row in the table, returning None
    // if the table is full.
    // Note that it returns the absolute address of the row, not the row index.
    fn allocate_row(&mut self) -> Option<u64> {
        self.free_list.pop()
    }
}

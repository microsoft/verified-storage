use crate::mem_pool::*;
use crate::table::*;

pub trait VolatileListNode {
    fn next(&self) -> Option<&Self>;
}

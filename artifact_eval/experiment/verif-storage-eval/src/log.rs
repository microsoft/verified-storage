use storage_node::multilog::multilogimpl_t::*;

pub const LOG_SIZE: usize = 1024 * 1024 * 1024 * 4;
// pub const LOG_SIZE: usize = 1024 * 1024;

pub trait PmemLog {
    fn initialize(file_name: String, log_size: usize) -> Result<Self, MultiLogErr>
    where
        Self: Sized;
    fn append(&mut self, buf: &[u8]) -> Result<(), MultiLogErr>;
    fn tell(&self) -> i64;
}

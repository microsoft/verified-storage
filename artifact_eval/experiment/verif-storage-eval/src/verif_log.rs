use crate::{
    log::PmemLog, pmem_map_file, pmem_memcpy_persist, pmem_unmap, pmemlog_errormsg,
    PMEM_FILE_CREATE,
};
use pmemlog::{main_t::InfiniteLogImpl, pmemspec_t::PersistentMemory};
use std::ffi::{c_void, CString};
use std::slice::from_raw_parts;
use storage_node::multilog::multilogimpl_t::MultiLogErr;

struct MappedPM {
    virt_addr: *mut u8,
    mapped_len: usize,
}

pub struct OldVerifLog {
    log: InfiniteLogImpl<MappedPM>,
}

impl PmemLog for OldVerifLog {
    fn initialize(file_name: String, log_size: usize) -> Result<Self, MultiLogErr>
    where
        Self: Sized,
    {
        let mut mapped_len = 0;
        let mut is_pm = 0;
        let file = CString::new(file_name).unwrap();
        let file = file.as_c_str();
        let addr = unsafe {
            pmem_map_file(
                file.as_ptr(),
                log_size,
                PMEM_FILE_CREATE.try_into().unwrap(),
                0666,
                &mut mapped_len,
                &mut is_pm,
            )
        };
        if is_pm == 0 {
            println!("{}", unsafe {
                CString::from_raw(pmemlog_errormsg() as *mut i8)
                    .into_string()
                    .unwrap()
            });
            panic!("failed to start log");
            // return Err(from_i32(errno()));
        }

        let mut mapped_pm = MappedPM {
            mapped_len,
            virt_addr: addr as *mut u8,
        };

        let _ = InfiniteLogImpl::setup(&mut mapped_pm, log_size.try_into().unwrap()).unwrap();
        let log_result = InfiniteLogImpl::start(mapped_pm, log_size.try_into().unwrap());
        match log_result {
            Ok(log) => Ok(Self { log }),
            Err(_) => panic!("failed to start log"),
        }
    }

    // TODO: better handling of verif log errors
    fn append(&mut self, buf: &[u8]) -> Result<(), MultiLogErr> {
        let (head, tail, capacity) = self.log.get_head_and_tail().unwrap();
        if capacity - (tail - head) <= buf.len().try_into().unwrap() {
            self.log.advance_head(tail.into()).unwrap();
        }
        let _ = self.log.append(&buf.to_vec()).unwrap();
        Ok(())
    }

    fn tell(&self) -> i64 {
        match self.log.get_head_and_tail() {
            Ok((_, tail, _)) => tail.try_into().unwrap(),
            Err(_) => panic!("failed to get log head and tail"),
        }
    }
}

impl Drop for MappedPM {
    fn drop(&mut self) {
        unsafe { pmem_unmap(self.virt_addr as *mut c_void, self.mapped_len) };
    }
}

impl PersistentMemory for MappedPM {
    fn read(&self, addr: u64, num_bytes: u64) -> Vec<u8> {
        let ptr = unsafe { self.virt_addr.offset(addr.try_into().unwrap()) };
        let slice = unsafe { from_raw_parts(ptr, num_bytes.try_into().unwrap()) };
        slice.to_vec()
    }

    // uses PMDK to perform the write
    fn write(&mut self, addr: u64, bytes: &[u8]) {
        let ptr = unsafe { self.virt_addr.offset(addr.try_into().unwrap()) };
        unsafe {
            pmem_memcpy_persist(
                ptr as *mut c_void,
                bytes.as_ptr() as *const c_void,
                bytes.len(),
            )
        };
    }
}

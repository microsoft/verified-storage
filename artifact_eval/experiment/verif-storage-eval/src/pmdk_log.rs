use crate::log::PmemLog;
use crate::{
    pmemlog_append, pmemlog_close, pmemlog_create, pmemlog_errormsg, pmemlog_nbyte, pmemlog_rewind,
    pmemlog_tell, PMEMlogpool,
};
use std::cell::UnsafeCell;
use std::ffi::{c_void, CString};
use storage_node::multilog::multilogimpl_t::*;
use storage_node::pmem::pmemspec_t::*;

pub struct PmdkLog<'a> {
    pool: &'a UnsafeCell<PMEMlogpool>,
    useable_size: usize,
}

impl<'a> PmemLog for PmdkLog<'a> {
    fn initialize(file_name: String, log_size: usize) -> Result<Self, MultiLogErr> {
        let file = CString::new(file_name).unwrap();
        let file = file.as_c_str();
        // PMEMLOG_MIN_POOL doesn't get a binding but it's 2MB
        let log = unsafe { pmemlog_create(file.as_ptr(), log_size, 0666) };
        if log.is_null() {
            println!("{}", unsafe {
                CString::from_raw(pmemlog_errormsg() as *mut i8)
                    .into_string()
                    .unwrap()
            });
            return Err(MultiLogErr::PmemErr {
                err: PmemError::CannotOpenPmFile,
            });
        }
        let useable_size = unsafe { pmemlog_nbyte(log) };
        Ok(Self {
            pool: unsafe { &*log.cast() },
            useable_size,
        })
    }

    fn append(&mut self, buf: &[u8]) -> Result<(), MultiLogErr> {
        let len = buf.len();
        // libpmemlog does not automatically wrap the log, so we have to manually
        // rewind to the beginning of the log when we run out of space
        let log_pos: usize = self.tell().try_into().unwrap();
        if self.useable_size - log_pos <= len {
            unsafe {
                pmemlog_rewind(self.pool.get());
            }
        }
        let raw_buffer = buf.as_ptr() as *const c_void;
        let result = unsafe { pmemlog_append(self.pool.get(), raw_buffer, len) };
        if result < 0 {
            println!("{}", unsafe {
                CString::from_raw(pmemlog_errormsg() as *mut i8)
                    .into_string()
                    .unwrap()
            });
            return Err(MultiLogErr::PmemErr {
                err: PmemError::PmdkError,
            });
        }
        Ok(())
    }

    fn tell(&self) -> i64 {
        unsafe { pmemlog_tell(self.pool.get()) }
    }
}

impl<'a> Drop for PmdkLog<'a> {
    fn drop(&mut self) {
        unsafe { pmemlog_close(self.pool.get()) };
    }
}

use crate::log::PmemLog;
use storage_node::multilog::multilogimpl_t::*;
use storage_node::pmem::device_t::*;
use storage_node::pmem::linux_pmemfile_t::*;
use storage_node::pmem::pmemspec_t::*;

// The VerifLog is a single log, implemented as a `MultiLogImpl` that consits
// of only one PM region.
pub struct VerifLog {
    log: MultiLogImpl<MappedPmRegions>,
}

impl PmemLog for VerifLog {
    fn initialize(file_name: std::string::String, log_size: usize) -> Result<Self, MultiLogErr>
    where
        Self: Sized,
    {
        let mut device =
            MappedPmDevice::new(file_name.as_str(), log_size)
                .map_err(|e| MultiLogErr::PmemErr { err: e })?;
        // obtain the device as a single region and set it up as a multilog with one l og
        let region = device
            .get_new_region(log_size.try_into().unwrap())
            .map_err(|e| {
                println!("{:?}", e);
                MultiLogErr::PmemErr { err: e }
            })?;
        let region = MappedPM::new(region).map_err(|e| {
            println!("{:?}", e);
            MultiLogErr::PmemErr { err: e }
        })?;
        let region_vec = vec![region];
        let mut region = MappedPmRegions::combine_regions(region_vec);

        let (_capacity, id) = MultiLogImpl::setup(&mut region).map_err(|e| {
            println!("{:?}", e);
            e
        })?;
        let log = MultiLogImpl::start(region, id).map_err(|e| {
            println!("{:?}", e);
            e
        })?;

        Ok(VerifLog { log })
    }

    fn tell(&self) -> i64 {
        match self.log.get_head_tail_and_capacity(0) {
            Ok((_, tail, _)) => tail.try_into().unwrap(),
            Err(_) => panic!("failed to get log head and tail"),
        }
    }

    fn append(&mut self, buf: &[u8]) -> Result<(), MultiLogErr> {
        let (head, tail, capacity) = self.log.get_head_tail_and_capacity(0).unwrap();
        let capacity_u128: u128 = capacity.into();
        if capacity_u128 - (tail - head) <= buf.len().try_into().unwrap() {
            self.log.advance_head(0, tail.into())?;
        }
        self.log.tentatively_append(0, buf)?;
        self.log.commit()
    }
}

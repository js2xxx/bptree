#![no_std]
#![feature(new_uninit)]
#![feature(bool_to_option)]
#![feature(result_into_ok_or_err)]
#![feature(maybe_uninit_slice)]
#![feature(maybe_uninit_extra)]
#![feature(exclusive_range_pattern)]
#![feature(destructuring_assignment)]
#![feature(core_intrinsics)]
#![feature(map_try_insert)]

pub mod map;
mod mem;

extern crate alloc;

#[macro_export]
macro_rules! offset_of {
    ($type:ty, $member:ident) => {
        #[allow(clippy::ref_in_deref)]
        #[allow(deref_nullptr)]
        #[allow(unused_unsafe)]
        unsafe {
            &((&*core::ptr::null::<$type>()).$member) as *const _ as usize
        }
    };
}

#[macro_export]
macro_rules! container_of {
    ($ptr:expr, $type:ty, $member:ident) => {
        ($ptr.cast::<u8>())
            .sub($crate::offset_of!($type, $member))
            .cast::<$type>()
    };
}

pub use map::BpTreeMap;

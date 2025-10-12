use typewit_gce::const_marker::Usize;
use typewit_gce::{gce_int_eq, TypeEq};

const fn main(){
    _ = gce_int_eq!(0u8, 0u16);


    _ = gce_int_eq!(0u8, 0u16, u32);


    let _: TypeEq<Usize<_>, Usize<_>> = gce_int_eq!(0, 0, u32);
}
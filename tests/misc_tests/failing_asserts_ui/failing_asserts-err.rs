#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

use typewit_gce::const_marker::U8;

const fn aaa(_: u8) -> u8 { 3 }
const fn bbb(_: u8) -> u8 { 5 }


const fn foo<const X: u8, const Y: u8>() 
where
    U8<{Y * (3 + X)}>:,
    U8<{Y * (5 + X)}>:,
    U8<{X * X}>:,
    U8<{1 / X}>:,
    U8<{(1 / X) * (1 / X)}>:,
    U8<{1 % X}>:,
    U8<{(1 % X) * (1 % X)}>:,
{
    _ = typewit_gce::gce_int_eq!(3u8, 5);

    _ = typewit_gce::gce_int_eq!(Y * (3 + X), Y * (5 + X));

    // uses power syntax
    _ = typewit_gce::gce_int_eq!(aaa(3) * aaa(3), 0);
    _ = typewit_gce::gce_int_eq!(X * X, 0);
    _ = typewit_gce::gce_int_eq!(1/X, 0);
    _ = typewit_gce::gce_int_eq!((1/X) * (1/X), 0);
    _ = typewit_gce::gce_int_eq!(1 % X, 0);
    _ = typewit_gce::gce_int_eq!((1 % X) * (1 % X), 0);

    _ = typewit_gce::gce_int_eq!(aaa(3) / self::bbb(5), aaa(3) / (2 + self::bbb(5)));

    _ = typewit_gce::gce_int_eq!(aaa(3) % self::bbb(5), aaa(3) % (2 + self::bbb(5)));

    _ = typewit_gce::gce_int_eq!({ aaa(3) + 1 }, { bbb(3) + 1 });
}


fn main() {}
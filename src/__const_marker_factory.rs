use typewit::{
    const_marker::{self as cm, ConstMarker, ConstMarkerEq},
    TypeEq,
};


use std::marker::PhantomData;



pub struct __ConstMarkerFactory<T>(PhantomData<T>);

impl<T> __ConstMarkerFactory<T> {
    pub const NEW: Self = Self(PhantomData);

    pub const fn new(_: &T, _: &T) -> Self {
        Self(PhantomData)
    }

    pub const fn infer_from_return<CmL, CmR>(self) -> TypeEq<CmL, CmR>
    where
        CmL: ConstMarker<Of = T>,
        CmR: ConstMarker<Of = T>,
    {
        loop {}
    }
}

macro_rules! impls {
    ($(($ty:ident $marker:ident))*) => ($(
        impl __ConstMarkerFactory<$ty> {
            #[track_caller]
            #[inline(always)]
            pub const fn get_equality_proof<const L: $ty, const R: $ty>(
                self
            ) -> TypeEq<cm::$marker<L>, cm::$marker<R>> {
                const { 
                    <cm::$marker<L> as ConstMarkerEq>::Equals::VAL.expect_eq(
                        "`typewit_gce::gce_int_eq` was passed a const expression whose value \
                          can be different in different uses"
                    ) 
                }
            }
        }
    )*)
}
impls! {
    (u8 U8) 
    (u16 U16) 
    (u32 U32) 
    (u64 U64) 
    (u128 U128) 
    (usize Usize) 
    (i8 I8) 
    (i16 I16) 
    (i32 I32) 
    (i64 I64) 
    (i128 I128) 
    (isize Isize)
}


























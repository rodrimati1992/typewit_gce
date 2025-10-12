use typewit::{
    const_marker::{self as cm, ConstMarker, CmEquals},
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
    ($ty:ident $marker:ident) => (
        impl __ConstMarkerFactory<$ty> {
            #[track_caller]
            #[inline(always)]
            pub const fn get_equality_proof<const L: $ty, const R: $ty>(
                self
            ) -> TypeEq<cm::$marker<L>, cm::$marker<R>> {
                crate::__GceIntEqHelper::<cm::$marker<L>, cm::$marker<R>>::VAL
            }
        }
    )
}

impls!{u8 U8}
impls!{u16 U16}
impls!{u32 U32}
impls!{u64 U64}
impls!{u128 U128}
impls!{usize Usize}
impls!{i8 I8}
impls!{i16 I16}
impls!{i32 I32}
impls!{i64 I64}
impls!{i128 I128}
impls!{isize Isize}























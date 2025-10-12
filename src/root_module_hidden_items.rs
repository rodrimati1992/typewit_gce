/// implementation detail of typewit_gce
/// 
#[doc(hidden)]
pub struct __GceIntEqHelper<T, L, R>{
    pub equal_consts: typewit::TypeEq<L, R>,
    int_ty: core::marker::PhantomData<T>,
}

const _: () = {
    use core::marker::PhantomData;
    use typewit::const_marker::{self as cm, ConstMarker, ConstMarkerOf, ConstMarkerEqOf};
    use typewit::TypeEq;

    impl<T, L, R> __GceIntEqHelper<T, L, R> {
        #[inline(always)]
        pub const fn infer_from_arg(self, _: &T, _: &T) -> Self {
            self 
        }

        #[inline(always)]
        pub const fn infer_from_return(self) -> TypeEq<L, R>
        where
            L: ConstMarkerOf<T>,
            R: ConstMarkerOf<T>,
        {
            self.equal_consts
        }
    }

    impl<T, L, R> __GceIntEqHelper<T, L, R>
    where
        L: ConstMarkerEqOf<T>,
        R: ConstMarkerEqOf<T>,
    {
        pub const NEW: Self = {
            let type_cmp = typewit::const_marker::CmEquals::<L, R>::VAL;
            let err_msg = "\
                \n\
                `typewit_gce::gce_int_eq` was passed a const expression whose value \
                 can be different in different uses\
                \n\n\
            ";

            let equal_consts = type_cmp.expect_eq(err_msg);

            Self {
                equal_consts,
                int_ty: PhantomData,
            }
        };
    }

    macro_rules! impls {
        ($ty:ident $marker:ident) => (
            impl<const L_VAL: $ty, const R_VAL: $ty> 
                __GceIntEqHelper<$ty, cm::$marker<L_VAL>, cm::$marker<R_VAL>> 
            {
                #[track_caller]
                #[inline(always)]
                pub const fn get_equality_proof<const LB_VAL: $ty, const RB_VAL: $ty> (
                    self
                ) -> TypeEq<cm::$marker<L_VAL>, cm::$marker<R_VAL>> 
                where                    
                    cm::$marker<LB_VAL>: Identity<Type = cm::$marker<L_VAL>>,
                    cm::$marker<RB_VAL>: Identity<Type = cm::$marker<R_VAL>>,
                {
                    typewit::type_fn!{
                        struct TypeEqFn;

                        impl<L, R> (L, R) => TypeEq<L, R>
                    }

                    const {
                        <cm::$marker<L_VAL> as Identity>::TYPE_EQ
                            .zip(<cm::$marker<R_VAL> as Identity>::TYPE_EQ)
                            .map(TypeEqFn)
                    }.to_left(self.equal_consts)
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


};


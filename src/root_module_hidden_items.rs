// defined to 
#[doc(hidden)]
pub struct __GceIntEqHelper<L, R>(L, R);

impl<L, R, T> __GceIntEqHelper<L, R>
where
    L: typewit::const_marker::ConstMarkerEq<Of = T>,
    R: typewit::const_marker::ConstMarkerEq<Of = T>,
{
    pub const VAL: typewit::TypeEq<L, R> = {
        use typewit::const_marker::ConstMarker;

        let type_cmp = typewit::const_marker::CmEquals::<L, R>::VAL;
        let err_msg = "\
            \n\
            `typewit_gce::gce_int_eq` was passed a const expression whose value \
             can be different in different uses\
            \n\n\
        ";

        type_cmp.expect_eq(err_msg)
    };
}

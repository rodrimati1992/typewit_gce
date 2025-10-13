use crate::misc_tests::test_utils::assert_type;

use typewit_gce::{
    const_marker as cm,
    gce_int_eq, TypeEq,
};


#[test]
fn working_type_inference_from_return_test() {
    const _: () = {        
        let _: TypeEq<cm::Usize<_>, cm::Usize<_>> = gce_int_eq!(3, 3);
        let _: TypeEq<cm::Isize<_>, cm::Isize<_>> = gce_int_eq!(3, 3);

        let _: TypeEq<cm::U8<_>, cm::U8<_>> = gce_int_eq!(3, 3);
        let _: TypeEq<cm::I8<_>, cm::I8<_>> = gce_int_eq!(3, 3);

        let _: TypeEq<cm::U16<_>, cm::U16<_>> = gce_int_eq!(3, 3);
        let _: TypeEq<cm::I16<_>, cm::I16<_>> = gce_int_eq!(3, 3);

        let _: TypeEq<cm::U32<_>, cm::U32<_>> = gce_int_eq!(3, 3);
        let _: TypeEq<cm::I32<_>, cm::I32<_>> = gce_int_eq!(3, 3);

        let _: TypeEq<cm::U64<_>, cm::U64<_>> = gce_int_eq!(3, 3);
        let _: TypeEq<cm::I64<_>, cm::I64<_>> = gce_int_eq!(3, 3);

        let _: TypeEq<cm::U128<_>, cm::U128<_>> = gce_int_eq!(3, 3);
        let _: TypeEq<cm::I128<_>, cm::I128<_>> = gce_int_eq!(3, 3);
    };
}




#[test]
fn working_type_inference_from_args_test() {
    macro_rules! testcase {
        ($marker:ident, $int_ty:ty, $with_suffix:literal, $without_suffix:literal) => (
            assert_type::<TypeEq<cm::$marker<{$without_suffix}>, cm::$marker<{$without_suffix}>>>(
                gce_int_eq!($without_suffix, $with_suffix)
            );

            assert_type::<TypeEq<cm::$marker<{$without_suffix}>, cm::$marker<{$without_suffix}>>>(
                gce_int_eq!($with_suffix, $without_suffix)
            );

            assert_type::<TypeEq<cm::$marker<{$without_suffix}>, cm::$marker<{$without_suffix}>>>(
                gce_int_eq!($with_suffix, $with_suffix)
            );

            assert_type::<TypeEq<cm::$marker<{$without_suffix}>, cm::$marker<{$without_suffix}>>>(
                gce_int_eq!($without_suffix, $without_suffix, $int_ty)
            );
        )
    }

    testcase!{Usize, usize, 3usize, 3}
    testcase!{Isize, isize, 3isize, 3}
    testcase!{U8, u8, 3u8, 3}
    testcase!{I8, i8, 3i8, 3}
    testcase!{U16, u16, 3u16, 3}
    testcase!{I16, i16, 3i16, 3}
    testcase!{U32, u32, 3u32, 3}
    testcase!{I32, i32, 3i32, 3}
    testcase!{U64, u64, 3u64, 3}
    testcase!{I64, i64, 3i64, 3}
    testcase!{U128, u128, 3u128, 3}
    testcase!{I128, i128, 3i128, 3}
}



#[test]
fn arbitrary_syntax_test() {
    assert_eq!(foo::<2>([3, 5, 8, 13, 21]), [3, 5, 8, 13, 21]);

    const fn foo<const N: usize>(arr: [u8; N + 3]) -> [u8; 3 + N] {
        macro_rules! three { () => {3} }

        TypeEq::NEW.in_array(gce_int_eq!(N + ({three!()}), ({three!()}) + N))
            .to_right(arr)
    }
}


// can't use generic function because "overly generic constant"...
#[test]
fn arbitrary_syntax_literals_test() {
    const N: usize = 2;

    let _: TypeEq<cm::Usize<5>, cm::Usize<5>> = gce_int_eq!(
        N + ({ 1usize + 0b10 }), 
        ({ 0o1usize + 0x2 }) + N
    );
}





















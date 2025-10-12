#[track_caller]
pub fn assert_type<Expected>(v: impl Sized) {
    assert_eq!(
        std::any::type_name_of_val(&v),
        std::any::type_name::<Expected>()
    );
}


#[test]
#[should_panic]
fn assert_type_test() {
    assert_type::<u16>(0u8);
}



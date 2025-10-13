use typewit_gce::gce_int_eq;


const fn func() -> usize { 
    0
}


#[test]
fn expr_metavariable_compiles() {
    macro_rules! testcase {
        ($l:expr, $r:expr) => (
            _ = gce_int_eq!($l, $r);
            _ = gce_int_eq!($l + 1, $r + 1);
            _ = gce_int_eq!(3 * $l, $r * 3);
        )
    }

    testcase!{2 + 3, 5u8}
    testcase!{func(), func()}
}

#[test]
fn lit_metavariable_compiles() {
    macro_rules! testcase {
        ($l:literal, $r:literal) => (
            _ = gce_int_eq!($l, $r);
            _ = gce_int_eq!($l + 1, $r + 1);
            _ = gce_int_eq!(3 * $l, $r * 3);
        )
    }

    testcase!{2, 2u8}
}

#[test]
fn expr_metavariable_is_parenthesized() {
    macro_rules! testcase {
        ($l:expr) => (
            _ = gce_int_eq!($l * 7, 35u8);
        )
    }

    testcase!{2 + 3}
}













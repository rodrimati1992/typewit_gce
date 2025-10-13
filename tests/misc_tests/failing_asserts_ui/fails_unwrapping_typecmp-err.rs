#[track_caller]
const fn sneaky() -> usize {
    std::panic::Location::caller().column() as usize
}


const fn foo<T>() {
    _ = typewit_gce::gce_int_eq!(sneaky(), sneaky());
}


fn main() {
    foo::<()>();
}




const _: () = {
    typewit_gce::gce_int_eq!(3 >> 5, 3 >> 5, i8);
    typewit_gce::gce_int_eq!(3 << 5, 3 << 5, i8);
    typewit_gce::gce_int_eq!(3 | 5, 3 | 5, i8);
    typewit_gce::gce_int_eq!(3 ^ 5, 3 ^ 5, i8);
    typewit_gce::gce_int_eq!(!3, !3, i8);
    typewit_gce::gce_int_eq!(3i8.wrapping_add(20), 3i8.wrapping_add(20), i8);
    typewit_gce::gce_int_eq!([3, 5][0], [3, 5][0], i8);
};


const _: () = {
    typewit_gce::gce_int_eq!(3 + !5, 3 + !5, i8);
    typewit_gce::gce_int_eq!(3 * !5, 3 * !5, i8);
    typewit_gce::gce_int_eq!(3 / !5, 3 / !5, i8);
};

fn main(){}
const N: u32 = 10;

fn rem_zero() {
    typewit_gce::gce_int_eq!(N % 0, 0u32);
    typewit_gce::gce_int_eq!((N + 4) % (N - N), 0u32);
}

fn div_zero() {
    typewit_gce::gce_int_eq!(N / 0, 0u32);
    typewit_gce::gce_int_eq!((N - 4) / (N - N), 0u32);
}



fn main(){}



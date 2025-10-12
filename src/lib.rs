//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
//! 
#![feature(generic_const_exprs)]
#![allow(incomplete_features)]

extern crate typewit_gce_proc_macros;

pub use typewit;

#[doc(no_inline)]
pub use typewit::*;


mod macros;


mod __const_marker_factory;


#[doc(hidden)]
pub mod __ {
    pub use core::compile_error;

    pub use crate::{
        __const_marker_factory::__ConstMarkerFactory,
    };

    pub use typewit_gce_proc_macros::{assert_equal, call_equality_proof_fn};
}

include!{"./root_module_hidden_items.rs"}





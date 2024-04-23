//! This file contains the definitions and `Serializable`
//! implementations for various log entry types for the
//! durable store. These are trusted because their structure,
//! and `Serializable` implementations, need to be manually
//! audited to ensure they accurately reflect their
//! byte-level Rust representations.

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

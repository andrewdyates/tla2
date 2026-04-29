// Copyright 2026 Dropbox
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Author: Andrew Yates
// BTOR2 format parser, IR, and CHC translation for hardware model checking.
//
// Reference: "BTOR2, BtorMC and Boolector 3.0" by Niemetz, Preiner, Wolf, Biere (CAV 2018).

pub mod bitblast;
pub(crate) mod bmc;
pub(crate) mod coi;
pub mod error;
pub mod parser;
pub mod portfolio;
pub(crate) mod simplify;
pub mod to_chc;
pub mod translate;
pub mod types;

pub use bitblast::{bitblast, bitblast_eligible, BitblastedCircuit};
pub use error::Btor2Error;
pub use parser::{parse, parse_btor2, parse_file};
pub use portfolio::{check_btor2_portfolio, PortfolioConfig, PortfolioStats, ResultPhase};
pub use to_chc::{check_btor2_adaptive, translate_to_chc, TranslationResult};
pub use translate::{check_btor2, Btor2CheckResult};
pub use types::{Btor2Line, Btor2Node, Btor2Program, Btor2Sort};

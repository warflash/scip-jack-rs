use super::Separator;

/// Mixed-integer rounding (MIR) cuts.
pub struct MixedIntegerRoundingSeparator {
    pub cuts_found: u32,
}

impl MixedIntegerRoundingSeparator {
    pub fn new() -> Self {
        Self { cuts_found: 0 }
    }
}

impl Separator for MixedIntegerRoundingSeparator {
    fn separate(&mut self, _lp_solution: &[f64]) -> u32 {
        // TODO: Generate MIR cuts
        0
    }
}

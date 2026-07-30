use super::Separator;

/// Gomory mixed-integer cuts derived from the LP tableau.
pub struct GomoryCutSeparator {
    pub cuts_found: u32,
}

impl GomoryCutSeparator {
    pub fn new() -> Self {
        Self { cuts_found: 0 }
    }
}

impl Separator for GomoryCutSeparator {
    fn separate(&mut self, _lp_solution: &[f64]) -> u32 {
        // TODO: Generate Gomory cuts from fractional LP basis rows
        0
    }
}

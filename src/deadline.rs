//! The solver's own wall-clock deadline, visible to the loops that cost seconds.
//!
//! # Why this exists rather than another parameter
//!
//! Every stage of this solver takes a deadline and checks it *between* the
//! things it calls. That is enough exactly when each thing it calls is cheap,
//! and it is not: a single call to the special-distance test is `|R|` Dijkstras,
//! a single shortest-path heuristic is `|R|` more, and a single dual ascent is a
//! sweep per terminal. On PACE Track 2's instance079 — 36,415 vertices, 145,635
//! edges and 16,808 terminals after a classical reduction that deletes nothing —
//! each of those is a minute or more inside one function call, and the solver
//! took 93.0 s under a **one-second** limit, 97.4 s under five and 98.2 s under
//! thirty. An overrun that does not move when the budget moves is the signature
//! of a stage that never asks what time it is.
//!
//! Threading `Option<Instant>` into each of those primitives means changing
//! every call site of each — the reduction, the branch-and-cut, the local
//! search, the recombination — for a parameter that always carries the same
//! value: the deadline of the solve in progress. So it is installed once, for
//! the duration of the call, and read where the work is.
//!
//! # What a reader of this deadline may do
//!
//! > **Proposition (consulting it cannot change an answer).** Every loop that
//! > reads it uses it only to *stop early*, and each such stop is a refusal that
//! > the caller already tolerates: a primal heuristic that stops returns no tree,
//! > which is the same as finding none; a dual ascent that stops returns the
//! > iterate it has, and every iterate of the ascent is a feasible dual and hence
//! > a valid bound; a reduction that stops performs a prefix of its deletions,
//! > and each deletion is justified independently of the others. ∎
//!
//! That is the same standing rule this repository applies to every other work
//! gate: *a deadline may refuse an attempt, but it may never change the answer of
//! a completed attempt.*
//!
//! # Scope
//!
//! The deadline is per-thread and is restored when [`Guard`] drops, so nested
//! installs behave like a stack and a caller that installs none leaves every
//! reader seeing `None` — which is what the unit tests and the probe binaries
//! do, and why none of them changes behaviour.

use std::cell::Cell;
use std::time::Instant;

thread_local! {
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
}

/// Restores the previous deadline when dropped.
///
/// Held by value at the top of a solve; nested solves (the tests run several)
/// therefore nest correctly rather than clobbering one another.
pub struct Guard(Option<Instant>);

impl Drop for Guard {
    fn drop(&mut self) {
        DEADLINE.with(|d| d.set(self.0));
    }
}

/// Install `deadline` for the current thread until the returned guard drops.
#[must_use = "the deadline is uninstalled when the guard drops"]
pub fn install(deadline: Option<Instant>) -> Guard {
    DEADLINE.with(|d| Guard(d.replace(deadline)))
}

/// Whether the installed deadline has passed. `false` when none is installed.
#[inline]
pub fn expired() -> bool {
    DEADLINE.with(|d| d.get()).is_some_and(|d| Instant::now() >= d)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn no_deadline_never_expires() {
        assert!(!expired());
    }

    #[test]
    fn an_installed_deadline_expires_and_is_restored() {
        assert!(!expired());
        {
            let _g = install(Some(Instant::now() - Duration::from_secs(1)));
            assert!(expired());
            {
                // Nested installs stack rather than clobber.
                let _inner = install(Some(Instant::now() + Duration::from_secs(3600)));
                assert!(!expired());
            }
            assert!(expired());
        }
        assert!(!expired(), "the guard did not restore the previous deadline");
    }
}

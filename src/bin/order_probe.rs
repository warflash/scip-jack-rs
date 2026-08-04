//! Does breaking the greedy's ties at random buy width?
//!
//! The width dynamic programme's cost is `work_estimate`, which is `3^w`-ish per
//! bag, so one width is a factor of three. Every ordering in the portfolio is a
//! greedy over a score with enormous ties, and the tie is currently broken by the
//! vertex's index — that is, by the order the input file listed it in. This probe
//! asks what that arbitrary choice is worth.
//!
//! ```text
//! order_probe <instance> [seconds] [cap]
//! ```
//!
//! emits one CSV row:
//!
//! ```text
//! name,V,E,R,det_width,det_work,rnd_width,rnd_work,samples,secs
//! ```
//!
//! `det_*` is the deterministic four-ordering portfolio; `rnd_*` is the best over
//! that plus seeded min-fill and min-degree-fill runs, drawn until the sampling
//! has cost as long as the dynamic programme the best plan so far implies. The
//! probe takes a hard cap and never runs without one.

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::steiner_td::{work_estimate, TD_UNITS_PER_SECOND, MAX_BAG};
use scip_jack::graph::algorithms::tree_decomposition::{
    decompose_portfolio, decompose_seeded, Ordering, ORDERINGS,
};
use scip_jack::graph::UndirectedGraph;
use scip_jack::preprocessing::preprocess_until;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: order_probe <instance> [seconds] [cap]");
        return;
    }
    let budget: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(30.0);
    let cap: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(MAX_BAG - 2);
    let hard = Instant::now() + Duration::from_secs_f64(budget);

    let name = std::path::Path::new(&args[1])
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();
    let Ok(instance) = scip_jack::io::read_instance(&args[1]) else {
        println!("{name},,,,,,,,,read-failed");
        return;
    };
    let mut g0 = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        g0.add_node(node.id, node.node_type, node.weight);
    }
    for e in &instance.edges {
        g0.add_edge(e.src, e.dst, e.cost);
    }
    let (rg, _) = preprocess_until(&instance, &g0, Some(Instant::now() + Duration::from_secs_f64(budget / 3.0)));
    let (ri, g) = rg.to_instance();
    let row = format!("{name},{},{},{}", ri.num_nodes, ri.num_edges, ri.terminals.len());

    // Per-ordering cost at the cap, which is what says whether one greedy may be
    // allowed to veto the others: `min-degree` is the cheap gate and the question
    // is what consulting the rest costs when it refuses.
    if std::env::var("SJ_PER_ORDER").is_ok() {
        print!("{row}");
        for &o in ORDERINGS.iter() {
            let t = Instant::now();
            let td = decompose_seeded(&g, o, cap, Some(hard), 0);
            print!(
                ",{o:?}:{}:{:.3}",
                td.map(|t| t.width as i64).unwrap_or(-1),
                t.elapsed().as_secs_f64()
            );
        }
        println!();
        return;
    }

    let det = decompose_portfolio(&g, cap, Some(hard), &ORDERINGS);
    let (mut best_w, mut best_work) = match &det {
        Some((td, w)) => (td.width as i64, *w),
        None => (-1, f64::INFINITY),
    };
    let (det_w, det_work) = (best_w, best_work);

    // Sample while the sampling has cost less than the DP the incumbent implies:
    // halving that DP is worth exactly that DP. Record the incumbent at a ladder
    // of elapsed times, which is what says whether the gain arrives fast enough
    // to be usable inside a five-second budget.
    let checkpoints = [0.05f64, 0.1, 0.25, 0.5, 1.0, 2.0, 4.0];
    let mut at: Vec<f64> = vec![f64::NAN; checkpoints.len()];
    let mut next = 0usize;
    let t0 = Instant::now();
    let mut samples = 0u32;
    let orders = [Ordering::MinFill, Ordering::MinDegreeFill, Ordering::FillWeighted];
    loop {
        let spent = t0.elapsed().as_secs_f64();
        while next < checkpoints.len() && spent >= checkpoints[next] {
            at[next] = best_work;
            next += 1;
        }
        let worth = if best_work.is_finite() { best_work / TD_UNITS_PER_SECOND } else { budget };
        if spent >= worth.min(budget) || Instant::now() >= hard {
            break;
        }
        let seed = 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(samples as u64 + 1) | 1;
        let order = orders[samples as usize % orders.len()];
        samples += 1;
        if let Some(td) = decompose_seeded(&g, order, cap, Some(hard), seed) {
            let w = work_estimate(&td, g.edges.len(), 1);
            if w < best_work {
                best_work = w;
                best_w = td.width as i64;
            }
        }
    }
    for a in at.iter_mut() {
        if a.is_nan() {
            *a = best_work;
        }
    }
    let ladder: Vec<String> = at.iter().map(|w| format!("{w:.2e}")).collect();
    println!(
        "{row},{det_w},{det_work:.3e},{best_w},{best_work:.3e},{samples},{:.2},{}",
        t0.elapsed().as_secs_f64(),
        ladder.join(",")
    );
}

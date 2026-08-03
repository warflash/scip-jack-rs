//! What does the bidirected cut relaxation cost when it is not an LP?
//!
//! Item 1 of the fourteenth round asks for two numbers and refuses to accept a
//! method scored against itself: *seconds to reach a given fraction of `LP*`*,
//! and *the value reached in one second*, on the instances where `LP*` is known
//! exactly. This probe produces both, for
//! [`scip_jack::model::flow_dual::FlowDual`] — projected supergradient ascent on
//! the flow dual, with no LP anywhere in the loop.
//!
//! ```text
//! flowdual_probe <instance> [optimum] [seconds cap] [lpstar]
//! ```
//!
//! `lpstar` is the converged root-LP value if one is known; the fractions are
//! reported against it, and against the optimum when it is not supplied.
//!
//! `SJ_FD_DEFLECTION`, `SJ_FD_GAMMA`, `SJ_FD_STALL` and `SJ_FD_BLIND` override the
//! method's constants so the two variants can be compared on the same tree
//! without rebuilding. `SJ_FD_BLIND=1` withholds the incumbent, which is the
//! honest measurement when the target is not available.
//!
//! One CSV row on stdout; the trajectory on stderr.

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::{dual_ascent_masked, ArcIndex};
use scip_jack::graph::{Cost, DirectedGraph, UndirectedGraph};
use scip_jack::model::{FlowDual, FlowDualOptions, FlowDualStop};
use scip_jack::preprocessing::preprocess_until;

fn envf(name: &str, default: f64) -> f64 {
    env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: flowdual_probe <instance> [optimum] [seconds cap] [lpstar]");
        return;
    }
    let opt: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(f64::NAN);
    let cap = Duration::from_secs_f64(args.get(3).and_then(|s| s.parse().ok()).unwrap_or(5.0));
    let lpstar: f64 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(opt);
    let name = std::path::Path::new(&args[1])
        .file_name()
        .map(|s| s.to_string_lossy().to_string())
        .unwrap_or_default();

    let instance = scip_jack::io::read_instance(&args[1]).expect("read");
    let mut graph = UndirectedGraph::new(instance.num_nodes);
    for node in &instance.nodes {
        graph.add_node(node.id, node.node_type, node.weight);
    }
    for edge in &instance.edges {
        graph.add_edge(edge.src, edge.dst, edge.cost);
    }
    let t_pre = Instant::now();
    let (rg, pr) = preprocess_until(&instance, &graph, None);
    let (ri, ru) = rg.to_instance();
    let pre_secs = t_pre.elapsed().as_secs_f64();
    let offset = pr.lower_bound_offset;
    let terminals = ri.terminals.clone();
    if terminals.len() < 2 {
        println!("{name},{opt},closed,,,,,,,,,,,,,,");
        return;
    }
    let directed = DirectedGraph::from_undirected(&ru);
    let idx = ArcIndex::new(&directed);
    let active = vec![true; idx.num_arcs()];

    let mut ascent = Cost::NEG_INFINITY;
    let mut best_root = terminals[0];
    for &r in &terminals {
        let v = dual_ascent_masked(&idx, r, &terminals, &active).lower_bound;
        if v > ascent {
            ascent = v;
            best_root = r;
        }
    }
    let root = if env::var("SJ_FD_BESTROOT").is_ok() { best_root } else { terminals[0] };

    let opts = FlowDualOptions {
        step_gamma: envf("SJ_FD_GAMMA", 2.0),
        deflection: envf("SJ_FD_DEFLECTION", 0.6),
        stall_window: envf("SJ_FD_STALL", 32.0) as u32,
        blind_target_slack: envf("SJ_FD_BLIND_SLACK", 0.05),
        entry_budget: envf("SJ_FD_ENTRIES", 0.0) as usize,
        restart_on_stall: envf("SJ_FD_RESTART", 0.0) != 0.0,
    };
    let blind = env::var("SJ_FD_BLIND").is_ok();

    eprintln!(
        "{name}: |V|={} |E|={} |R|={} arcs={} entries={} offset={offset:.1} \
         ascent={:.1} pre={pre_secs:.2}s",
        ri.num_nodes,
        ri.num_edges,
        terminals.len(),
        idx.num_arcs(),
        (terminals.len() - 1) * idx.num_arcs(),
        ascent + offset
    );

    let t_build = Instant::now();
    let mut fd = match FlowDual::new(&idx, root, &terminals, opts) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("  refused: {e:?}");
            println!("{name},{opt},refused,,,,,,,,,,,,,,");
            return;
        }
    };
    let build_secs = t_build.elapsed().as_secs_f64();
    // The target the solver would have: its incumbent. Reduced-space value.
    let target = if blind || !opt.is_finite() { None } else { Some(opt - offset) };
    fd.set_target(target);

    // Trajectory: the best value at a geometric ladder of wall-clock marks.
    let marks = [0.05, 0.1, 0.25, 0.5, 1.0, 2.0, 3.0, 5.0, 10.0, 30.0, 100.0];
    let started = Instant::now();
    let deadline = started + cap;
    let mut traj: Vec<(f64, Cost)> = Vec::new();
    let mut stop = FlowDualStop::Deadline;
    let mut mi = 0usize;
    let seed_value = {
        // The seed's own value, before any step, re-derived.
        let v = fd.finish(&idx);
        v + offset
    };
    while Instant::now() < deadline {
        let next = marks.get(mi).copied().unwrap_or(f64::INFINITY);
        let sub = started + Duration::from_secs_f64(next.min(cap.as_secs_f64()));
        stop = fd.ascend(&idx, Cost::INFINITY, sub.min(deadline), u64::MAX, 8);
        let el = started.elapsed().as_secs_f64();
        traj.push((el, fd.bound() + offset));
        mi += 1;
        if !matches!(stop, FlowDualStop::Deadline) {
            break;
        }
        if mi >= marks.len() {
            break;
        }
    }
    let wall = started.elapsed().as_secs_f64();
    let value = fd.finish(&idx) + offset;
    let st = fd.stats();

    let frac = |v: Cost| if lpstar.is_finite() && lpstar != 0.0 { v / lpstar } else { f64::NAN };
    // First mark at which the trajectory crossed each fraction of LP*.
    let cross = |f: f64| -> f64 {
        for &(t, v) in traj.iter() {
            if lpstar.is_finite() && lpstar != 0.0 && v / lpstar >= f {
                return t;
            }
        }
        f64::NAN
    };
    let at = |sec: f64| -> Cost {
        let mut last = Cost::NEG_INFINITY;
        for &(t, v) in traj.iter() {
            if t <= sec + 1e-9 {
                last = v;
            }
        }
        last
    };

    for (t, v) in traj.iter() {
        eprintln!("    t {t:8.3}s  bound {:14.2}  frac {:.6}", v, frac(*v));
    }
    eprintln!(
        "  seed {seed_value:.1} -> {value:.1} ({:.6} of LP*={lpstar:.1}) in {wall:.2}s, \
         {} iterations, {} oracle calls in {:.2}s, step {:.2}s, {} projections, stop {stop:?}",
        frac(value),
        st.iterations,
        st.oracle_calls,
        st.oracle_secs,
        st.step_secs,
        st.projected_arcs
    );

    println!(
        "{name},{opt},{lpstar},{:.1},{seed_value:.1},{value:.1},{:.6},{:.6},\
         {:.3},{:.3},{:.3},{:.3},{:.1},{:.1},{:.1},{},{:.3},{stop:?},{},{},{:.3},{build_secs:.3},{pre_secs:.3}",
        ascent + offset,
        frac(value),
        if opt.is_finite() && opt != 0.0 { value / opt } else { f64::NAN },
        cross(0.99),
        cross(0.999),
        cross(0.9999),
        cross(1.0),
        at(0.25),
        at(1.0),
        at(3.0),
        st.iterations,
        wall,
        idx.num_arcs(),
        terminals.len(),
        st.oracle_secs,
    );
}

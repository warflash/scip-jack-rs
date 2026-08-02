//! What is the root cut relaxation actually worth, and where does the time go?
//!
//! Two questions the notes never contained an answer to, and everything about
//! how the LP-derived potential should be funded turns on the first.
//!
//! **1. `LP*` — the relaxation's own optimum.** The separation loop is run to
//! *convergence* with no clock limit: rounds continue until a round installs
//! nothing, which is the point at which the LP point satisfies every inequality
//! any separator here can express. The connectivity separator is exact — it is a
//! max flow per terminal — so a converged loop over the connectivity family alone
//! has solved the model's own relaxation exactly:
//!
//! > Let `z` be the optimum over the rows currently in the model, attained at
//! > `y*`. The model is a relaxation of the full cut formulation, so `z <= LP*`.
//! > If no separator finds a violated row then `y*` is feasible for the full
//! > formulation, so `z >= LP*`. Hence `z = LP*`. ∎
//!
//! Both values are reported: the connectivity-only optimum, which is the model's
//! relaxation as stated, and the optimum after the cycle, partition and
//! terminal-free families are also exhausted, which is a strictly stronger
//! relaxation and therefore a different number.
//!
//! **2. Where the seconds go.** Per round: simplex, connectivity separation,
//! the other three separators, the dual harvest, and everything else — which is
//! the model surgery, the row installation and the pruning rebuilds. "The LP is
//! slow" is not a statement anything could act on until it says which of the
//! five.
//!
//! ```text
//! lpstar_probe <instance> [optimum] [seconds cap]
//! ```
//!
//! Emits one CSV row on stdout and the round trace on stderr. `SJ_LP_METHOD=simplex`
//! forces the dual simplex; the default is the interior point, which is the only
//! algorithm that converges on the wide-cost-range instances (see §76).

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::{dual_ascent_masked, ArcIndex};
use scip_jack::graph::{Cost, DirectedGraph, NodeId, UndirectedGraph};
use scip_jack::model::{LpMethod, RootCertificate, RootSeparation};
use scip_jack::preprocessing::preprocess_until;

struct Run {
    bound: Cost,
    packing: Cost,
    converged: bool,
    solves: u64,
    rows: usize,
    rounds: usize,
    wall: f64,
    lp_secs: f64,
    flow_secs: f64,
    extra_secs: f64,
    harvest_secs: f64,
    rebuilds: u64,
}

fn converge(
    directed: &DirectedGraph,
    root: NodeId,
    terminals: &[NodeId],
    extra_families: bool,
    method: LpMethod,
    cap: Duration,
) -> Run {
    let build_started = Instant::now();
    let mut sep = RootSeparation::new(directed, root, terminals);
    let build_secs = build_started.elapsed().as_secs_f64();
    sep.extra_families = extra_families;
    sep.set_method(method);
    let started = Instant::now();
    let deadline = started + cap;
    // One `advance` with a huge round budget: the loop stops of its own accord
    // when it converges, and only the cap can cut it short.
    let cert: Option<RootCertificate> =
        sep.advance(Cost::INFINITY, deadline, 1_000_000, 1 << 24);
    let wall = started.elapsed().as_secs_f64();
    let (bound, packing, rounds, lp, flow, extra, harvest, rebuilds) = match &cert {
        Some(c) => {
            let lp: f64 = c.rounds.iter().map(|r| r.lp_secs).sum();
            let flow: f64 = c.rounds.iter().map(|r| r.flow_secs).sum();
            let extra: f64 = c.rounds.iter().map(|r| r.extra_secs).sum();
            let harvest: f64 = c.rounds.iter().map(|r| r.harvest_secs).sum();
            let rebuilds = c.rounds.last().map_or(0, |r| r.rebuilds);
            (
                c.lp_bound,
                c.packing.value,
                c.rounds.len(),
                lp,
                flow,
                extra,
                harvest,
                rebuilds,
            )
        }
        None => (Cost::NEG_INFINITY, 0.0, 0, 0.0, 0.0, 0.0, 0.0, 0),
    };
    if let Some(c) = &cert {
        let last = c.rounds.len().saturating_sub(1);
        for (i, r) in c.rounds.iter().enumerate() {
            if i < 6 || i % 32 == 0 || i + 6 >= last {
                eprintln!(
                    "    round {i:5}  bound {:12.2}  rows {:6}  struct {:5}  cuts {:4}  \
                     lp {:6.3}  flow {:6.3}  extra {:6.3}  harv {:6.3}  tot {:6.3}",
                    r.bound, r.rows, r.structural, r.cuts, r.lp_secs, r.flow_secs, r.extra_secs,
                    r.harvest_secs, r.secs
                );
            }
        }
    }
    let round_secs: f64 = cert.as_ref().map_or(0.0, |c| c.rounds.iter().map(|r| r.secs).sum());
    eprintln!(
        "    [split] build {build_secs:.2}s  rounds {round_secs:.2}s  advance {:.2}s  \
         unaccounted {:.2}s  solves {}  rounds {rounds}",
        wall,
        wall - round_secs,
        sep.lp_solves()
    );
    Run {
        bound,
        packing,
        converged: sep.is_converged(),
        solves: sep.lp_solves(),
        rows: sep.num_rows(),
        rounds,
        wall,
        lp_secs: lp,
        flow_secs: flow,
        extra_secs: extra,
        harvest_secs: harvest,
        rebuilds,
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: lpstar_probe <instance> [optimum] [seconds cap]");
        return;
    }
    let opt: f64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(f64::NAN);
    let cap = Duration::from_secs_f64(
        args.get(3).and_then(|s| s.parse().ok()).unwrap_or(300.0),
    );
    let method = match std::env::var("SJ_LP_METHOD").as_deref() {
        Ok("simplex") => LpMethod::Simplex,
        _ => LpMethod::InteriorPoint,
    };
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
    let (rg, pr) = preprocess_until(&instance, &graph, None);
    let (ri, ru) = rg.to_instance();
    let offset = pr.lower_bound_offset;
    let terminals = ri.terminals.clone();
    if terminals.len() < 2 {
        println!("{name},{opt},closed,,,,,,,,,,,,,,,,,,");
        return;
    }
    let directed = DirectedGraph::from_undirected(&ru);
    let idx = ArcIndex::new(&directed);
    let active = vec![true; idx.num_arcs()];

    // The strongest ascent available, over every terminal as root. This is the
    // floor the loop's reported bound may never fall below.
    let mut ascent = Cost::NEG_INFINITY;
    for &r in &terminals {
        ascent = ascent.max(dual_ascent_masked(&idx, r, &terminals, &active).lower_bound);
    }
    let root = terminals[0];

    eprintln!(
        "{name}: |V|={} |E|={} |R|={} offset={offset:.1} ascent={:.1}",
        ri.num_nodes,
        ri.num_edges,
        terminals.len(),
        ascent + offset
    );
    eprintln!("  connectivity family only:");
    let bcr = converge(&directed, root, &terminals, false, method, cap);
    eprintln!("  all four families:");
    let all = converge(&directed, root, &terminals, true, method, cap);

    let ratio = |v: f64| if opt.is_finite() && opt != 0.0 { (v + offset) / opt } else { f64::NAN };
    println!(
        "{name},{opt},{:.1},{:.1},{:.1},{:.6},{},{},{},{:.2},{:.2},{:.2},{:.2},{:.2},{},\
         {:.1},{:.6},{},{},{:.2},{:.2},{:.1}",
        ascent + offset,
        bcr.bound + offset,
        bcr.packing + offset,
        ratio(bcr.bound),
        bcr.converged,
        bcr.solves,
        bcr.rounds,
        bcr.wall,
        bcr.lp_secs,
        bcr.flow_secs,
        bcr.extra_secs,
        bcr.harvest_secs,
        bcr.rebuilds,
        all.bound + offset,
        ratio(all.bound),
        all.converged,
        all.solves,
        all.wall,
        all.lp_secs,
        all.packing + offset,
    );
    eprintln!(
        "  BCR* {:.1} ({:.4} of opt) rows {} solves {} in {:.2}s \
         [lp {:.2} flow {:.2} extra {:.2} harv {:.2} rebuilds {}] converged {}",
        bcr.bound + offset,
        ratio(bcr.bound),
        bcr.rows,
        bcr.solves,
        bcr.wall,
        bcr.lp_secs,
        bcr.flow_secs,
        bcr.extra_secs,
        bcr.harvest_secs,
        bcr.rebuilds,
        bcr.converged
    );
    eprintln!(
        "  ALL* {:.1} ({:.4} of opt) rows {} solves {} in {:.2}s \
         [lp {:.2} flow {:.2} extra {:.2} harv {:.2} rebuilds {}] converged {}",
        all.bound + offset,
        ratio(all.bound),
        all.rows,
        all.solves,
        all.wall,
        all.lp_secs,
        all.flow_secs,
        all.extra_secs,
        all.harvest_secs,
        all.rebuilds,
        all.converged
    );
}

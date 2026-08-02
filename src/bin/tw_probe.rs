//! Reports the width of a heuristic tree decomposition of a *reduced* instance.
//!
//! The question this answers is whether a Steiner dynamic programme over a tree
//! decomposition is affordable, and that is a question about the graph the
//! solver actually hands to its exact stage, not about the file on disk. So it
//! runs the same classical reduction fixpoint the solver runs, then decomposes.
//!
//! ```text
//! tw_probe <instance> [max width] [seconds]
//! ```

use std::env;
use std::time::{Duration, Instant};

use scip_jack::graph::algorithms::tree_decomposition::{decompose_with, Ordering};
use scip_jack::graph::UndirectedGraph;
use scip_jack::preprocessing::preprocess_until;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: tw_probe <instance> [max width] [seconds]");
        return;
    }
    let max_width: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(48);
    let budget: f64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(60.0);

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
    let t0 = Instant::now();
    let (rg, _) = preprocess_until(&instance, &graph, None);
    let (ri, ru) = rg.to_instance();
    let reduce_secs = t0.elapsed().as_secs_f64();

    let mut row = format!(
        "{name},{},{},{},{:.2}",
        ri.num_nodes,
        ri.num_edges,
        ri.terminals.len(),
        reduce_secs
    );
    let t = Instant::now();
    let lb = scip_jack::graph::algorithms::tree_decomposition::treewidth_lower_bound(&ru);
    row.push_str(&format!(",{lb},{:.2}", t.elapsed().as_secs_f64()));
    // The whole width/work Pareto frontier, not only the narrowest point.
    for order in scip_jack::graph::algorithms::tree_decomposition::ORDERINGS {
        let t = Instant::now();
        let deadline = Some(Instant::now() + Duration::from_secs_f64(budget));
        match decompose_with(&ru, order, max_width, deadline) {
            Some(td) => {
                assert!(td.verify(&ru), "decomposition failed its own axioms");
                let w = scip_jack::graph::algorithms::steiner_td::work_estimate(
                    &td,
                    ru.edges.len(),
                    1,
                );
                row.push_str(&format!(",{},{:.1e},{:.2}", td.width, w, t.elapsed().as_secs_f64()));
            }
            None => row.push_str(&format!(",>{max_width},,{:.2}", t.elapsed().as_secs_f64())),
        }
    }
    // And what the exact width-parameterised DP costs on the one the portfolio
    // picks, which is the question the widths were measured to answer.
    let t = Instant::now();
    let td = scip_jack::graph::algorithms::tree_decomposition::decompose(&ru, max_width, None);
    let _ = Ordering::MinFill;
    match td {
        Some(td) => {
            let work = scip_jack::graph::algorithms::steiner_td::work_estimate(&td, ru.edges.len(), 1);
            let t2 = Instant::now();
            match scip_jack::graph::algorithms::steiner_tree_over_decomposition(
                &ru, &ri.terminals, &td, 40_000_000, false, None,
            ) {
                Some((cost, edges)) => row.push_str(&format!(
                    ",{:.0},{},{:.2},{:.1e}",
                    cost, edges.len(), t2.elapsed().as_secs_f64(), work
                )),
                None => row.push_str(&format!(",capped,,{:.2},{:.1e}", t2.elapsed().as_secs_f64(), work)),
            }
        }
        None => row.push_str(",toowide,,,"),
    }
    let _ = t;
    // What the join actually did, which is the quantity any replacement for it
    // has to be judged against.
    let js = scip_jack::graph::algorithms::steiner_td::take_join_stats();
    row.push_str(&format!(
        ",{},{},{:.0},{},{},{},{:.2},{},{}",
        js.joins,
        js.classes,
        js.pairs_available,
        js.pairs_popped,
        js.emitted,
        js.saturated,
        js.nanos as f64 / 1e9,
        js.unary_nodes,
        js.unary_states,
    ));
    println!("{row}");
}

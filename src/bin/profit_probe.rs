//! Does the implied-profit reduction have anything to work with?
//!
//! Reports, for the graph as read and again after the classical fixpoint, how
//! many edges carry a positive implied profit, how large the largest is, and
//! how many edges one sweep of the rule deletes.
//!
//! ```text
//! profit_probe <instance>
//! ```

use std::env;
use std::time::Instant;

use scip_jack::graph::UndirectedGraph;
use scip_jack::preprocessing::csr::Csr;
use scip_jack::preprocessing::implied_profit::{implied_profit_reductions, implied_profits};
use scip_jack::preprocessing::{preprocess_until, ReducibleGraph};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: profit_probe <instance>");
        return;
    }
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

    let report = |tag: &str, rg: &mut ReducibleGraph| {
        let csr = Csr::build(rg);
        let p = implied_profits(rg, &csr);
        let live: Vec<u32> = rg.valid_edges();
        let mut positive = 0usize;
        let mut best = 0.0f64;
        for &e in &live {
            let v = p.get(e);
            if v > 0.0 {
                positive += 1;
                best = best.max(v);
            }
        }
        let t0 = Instant::now();
        let removed = implied_profit_reductions(rg);
        println!(
            "{name},{tag},V={},E={},R={},profit_edges={positive},max_profit={best:.1},deleted={removed},secs={:.2}",
            rg.num_valid_nodes(),
            rg.num_valid_edges(),
            rg.terminals.len(),
            t0.elapsed().as_secs_f64(),
        );
    };

    let mut raw = ReducibleGraph::from_instance(&instance, &graph);
    report("raw", &mut raw);

    let (mut rg, _) = preprocess_until(&instance, &graph, None);
    report("reduced", &mut rg);
}

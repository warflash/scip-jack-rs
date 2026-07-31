# SCIP-Jack research paper index

Collected for the mathematical research memo in [`../SCIP_JACK_MATH_RESEARCH.md`](../SCIP_JACK_MATH_RESEARCH.md).

## Conversion method

- PDFs were checked for a `%PDF-` header and parsed with `pypdf 6.10.0`.
- Text was written as UTF-8 with a BOM so Unicode formulas, symbols, and ligatures are preserved when opened by Windows tools.
- Each extracted file contains `SOURCE`, `PAGES`, `EXTRACTOR`, and `===== PAGE n =====` markers.
- `pdfplumber 0.11.9` was retained as a fallback for pages on which the primary extractor returns no text. No fallback pages were needed in the current set.
- First pages were rendered with Poppler `pdftoppm` as a visual sanity check. Rendering reported missing display-font warnings for some legacy PDFs, but all valid PDFs rendered successfully.

## Downloaded and extracted papers

| Paper | PDF | Raw text | Why it matters | Original/source link |
| --- | --- | --- | --- | --- |
| Bonnet & Sikora (2019), *The PACE 2018 Parameterized Algorithms and Computational Experiments Challenge: The Third Iteration* | [PDF](downloads/BonnetSikora2019_PACE2018Report.pdf) | [TXT](extracted/BonnetSikora2019_PACE2018Report.txt) | Parameterized and computational Steiner algorithms; treewidth/small-parameter context | [Dagstuhl publication](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.IPEC.2018.26) |
| Byrka, Grandoni & Traub (2024), *The Bidirected Cut Relaxation for Steiner Tree has Integrality Gap Smaller than 2* | [PDF](downloads/ByrkaGrandoniTraub2024_BCRGap.pdf) | [TXT](extracted/ByrkaGrandoniTraub2024_BCRGap.txt) | Modern BCR integrality-gap theory; identifies fractional structure relevant to stronger bounds | [arXiv:2407.19905](https://arxiv.org/abs/2407.19905) |
| Dreyfus & Wagner (1971), *The Steiner Problem in Graphs* | [PDF](downloads/DreyfusWagner1971_SteinerProblemInGraphs.pdf) | [TXT](extracted/DreyfusWagner1971_SteinerProblemInGraphs.txt) | Exact dynamic programming parameterized by the number of terminals | [Direct PDF mirror](https://web.vu.lt/mif/s.jukna/tropical/Dreyfus-Wagner.pdf) |
| Goemans & Myung (1993), *A Catalog of Steiner Tree Formulations* | [PDF](downloads/GoemansMyung1993_CatalogOfSteinerTreeFormulations.pdf) | [TXT](extracted/GoemansMyung1993_CatalogOfSteinerTreeFormulations.txt) | Relationships among directed-cut, BCR, flow, and vertex-weighted formulations | [MIT-hosted PDF](https://math.mit.edu/~goemans/PAPERS/GoemansMyung-1993-ACatalogOfSteinerTreeFormulations.pdf) |
| Hougardy, Silvanus & Vygen (2014), *Dijkstra meets Steiner* | [PDF](downloads/HougardySilvanusVygen2014_DijkstraMeetsSteiner.pdf) | [TXT](extracted/HougardySilvanusVygen2014_DijkstraMeetsSteiner.txt) | Goal-oriented exact DP and future-cost pruning | [arXiv:1406.0492](https://arxiv.org/abs/1406.0492) |
| Jansen & Swennenhuis (2024), *Steiner Tree Parameterized by Multiway Cut and Even Less* | [PDF](downloads/JansenSwennenhuis2024_MultiwayCutSteiner.pdf) | [TXT](extracted/JansenSwennenhuis2024_MultiwayCutSteiner.txt) | Structural parameterization by terminal-separating cuts | [arXiv:2406.19819](https://arxiv.org/abs/2406.19819) |
| Ljubić (2021), *Solving Steiner Trees - Recent Advances, Challenges, and Perspectives* | [PDF](downloads/Ljubic2021_SteinerTreesSurvey.pdf) | [TXT](extracted/Ljubic2021_SteinerTreesSurvey.txt) | Broad survey connecting exact, approximate, polyhedral, and variant methods | [Author-hosted PDF](https://rishikeshavan.github.io/prof-ivana-site/docs/publications/NetworksSI.pdf) |
| Paschmanns & Traub (2026), *The Bidirected Cut Relaxation for Steiner Tree: Better Integrality Gap Bounds and the Limits of Moat Growing* | [PDF](downloads/PaschmannsTraub2026_BCRGap.pdf) | [TXT](extracted/PaschmannsTraub2026_BCRGap.txt) | Newer BCR gap bound and limits of a central approximation technique | [arXiv:2602.19879](https://arxiv.org/abs/2602.19879) |
| Rehfeldt & Koch (2021/2023), *Implications, conflicts, and reductions for Steiner trees* | [PDF](downloads/RehfeldtKoch2023_ImplicationsConflictsReductions.pdf) | [TXT](extracted/RehfeldtKoch2023_ImplicationsConflictsReductions.txt) | Strong modern exact reductions, implications, and conflicts | [Springer DOI](https://doi.org/10.1007/s10107-021-01757-5) |
| Rehfeldt & Koch (2018 report/preprint), *Reduction-based exact solution of prize-collecting Steiner tree problems* | [PDF](downloads/RehfeldtKoch2021_PCSTP.pdf) | [TXT](extracted/RehfeldtKoch2021_PCSTP.txt) | PCSTP/RPCSTP reductions and exact branch-and-bound ideas | [arXiv:1811.09068](https://arxiv.org/abs/1811.09068) |
| Chakrabarty, Könemann & Pritchard (2013), *Hypergraphic LP Relaxations for Steiner Trees* | [PDF](downloads/ChakrabartyKonemannPritchard2011_HypergraphicLP.pdf) | [TXT](extracted/ChakrabartyKonemannPritchard2011_HypergraphicLP.txt) | Partition/hypergraphic relaxations, uncrossing, sparse basic solutions, and relation to BCR | [Author-hosted PDF](https://www.cs.dartmouth.edu/~deepc/PUBS/CKP-full.pdf) |

## Papers already in the repository

| Paper | PDF | Raw text |
| --- | --- | --- |
| Gamrath, Koch, Maher, Rehfeldt & Shinano, *SCIP-Jack - A solver for STP and variants with parallelization extensions* | [PDF](GamrathKochMaherRehfeldtShinano.pdf) | [TXT](extracted/GamrathKochMaherRehfeldtShinano.txt) |
| Gamrath, Koch, Rehfeldt & Shinano, *SCIP-Jack - A massively parallel STP solver*, ZIB Report 14-35 | [PDF](ZR14-35.pdf) | [TXT](extracted/ZR14-35.txt) |

## Unavailable source

Wong (1984), *A Dual Ascent Approach for Steiner Tree Problems on a Directed Graph*, is referenced by the memo because it is the classic dual-ascent source. The publisher DOI page and the available ResearchGate author mirror returned access/HTML responses rather than a valid PDF during collection. The invalid HTML response was moved to `downloads/Wong1984_DualAscentSteiner.blocked.html` and is intentionally not presented as a paper. Metadata and abstract are available at the [ResearchGate record](https://www.researchgate.net/publication/225945384_A_dual_ascent_approach_for_steiner_tree_problems_on_a_directed_graph) and [Springer DOI](https://doi.org/10.1007/BF02612335).

## Notes on scope

This set includes the papers directly used in the research memo and the two SCIP-Jack papers already present in the repository. It does not attempt to recursively download every citation contained in each paper; that would be a substantially larger literature corpus. The index is intended to be a reproducible first research bundle.

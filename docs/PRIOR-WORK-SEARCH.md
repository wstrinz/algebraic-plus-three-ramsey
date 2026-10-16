# Prior-work search log (Theorem B(b))

**Result: no prior statement of Theorem B(b) was found**, that is, of "finitely many points on a
circle, all with algebraic coordinates except at most three arbitrary points, form a Euclidean
Ramsey set", or of the Ramsey status of the class in Theorem A.10 of the appendix of Pálvölgyi's
arXiv:2609.23327. This is a search result, not a proof of novelty. The searches were made by AI
agents (Claude Sonnet 5.5; see `DISCLOSURE.md`): four sweeps for the spherical-ramsey release on
2026-10-12 and 2026-10-13, and a repeat for this package on **2026-10-16, 01:12 to 01:27 UTC**,
logged below.

## Repeat search, 2026-10-16

**arXiv** (API at export.arxiv.org, which matches titles, abstracts and metadata; and the listing
pages):

| Query | Hits | Relevant |
|---|---|---|
| `all:"Euclidean Ramsey"`, newest first | 31 (newest 2608.11736) | none beyond the credited work |
| `all:Ramsey AND all:concyclic` | 0 | |
| `all:Ramsey AND all:circle AND all:algebraic` | 1 | no |
| `abs:"non-Ramsey"` | 6 | no |
| `all:"2609.23327"` | 0 | (the API does not index citations) |
| `all:Palvolgyi AND all:Ramsey` | 4 | no new statement |
| `all:Ramsey AND all:heptagon` | 2 | no new statement |
| `all:Ramsey AND (cat:math.CO OR cat:math.MG)`, newest first | 1785 | the newest checked; none relevant |
| `arxiv.org/list/math.CO/new`, `arxiv.org/list/math.MG/new` (announcements of 2026-10-15) | about 90 and 12 entries | none on Euclidean Ramsey sets |

The latest math.CO / math.MG submissions indexed were dated 2026-10-14; the two Ramsey papers
among them (2610.20577, 2610.20545) are on graph and poset Ramsey numbers. No submission dated
2026-10-15 was indexed yet. The recent Euclidean Ramsey papers read (2608.11736, 2608.09649,
2606.13472, 2608.10865, 2504.10687 and 2609.23327) do not state Theorem B(b).

**GitHub** (`gh search repos` and `gh search code`):

- Repository queries: "Euclidean Ramsey", "EuclideanRamsey", "concyclic Ramsey", "cyclic Ramsey",
  "alg_plus_three", "FieldCriterion", "openai math 172", "Palvolgyi heptagon", "non-Ramsey
  heptagon", "Ramsey spherical sets", "Ramsey Lean 4", "Euclidean Ramsey Lean", "Erdos 174",
  "Graham conjecture spherical Ramsey", "Ramsey transitive sets", "openai-math-extensions", and
  "Ramsey" sorted by last update (40 repositories, all updated since 2026-09-23).
- Code queries: "Euclidean Ramsey", "EuclideanRamsey", "alg_plus_three", "cyclic Ramsey",
  "Palvolgyi heptagon", "non-Ramsey heptagon", "FieldCriterion", "concyclic Ramsey", "Ramsey
  concyclic algebraic".
- Hits on Euclidean Ramsey sets: openai/math (result 172: at most five points on a circle are
  Ramsey, nine circle points with algebraically independent parameters are not, cospherical sets),
  this author's own repositories, JD-Jones-ASES/six-concyclic-lean (at most six concyclic points;
  small spherical sets; algebraic spanning sets), and plasma-ai/erdos (a wiki of Erdős problems
  whose problem 174 page summarises Pálvölgyi's heptagon and OpenAI's results). None states the
  algebraic-plus-three theorem. Rogerhu12/openai-math-extensions and atimics/math2 (the algebraic
  case, credited in `README.md`) have no code hits for concyclic or cyclic sets.

**Palomar registry**: `https://data.palomar-registry.org/recent.json`, fetched 01:15 UTC (200
entries, 2026-09-30 to 2026-10-16). Euclidean Ramsey entries: PALOMAR-2026-10-14-000008
(mobius-ramsey, this author) and PALOMAR-2026-10-07-000011 (JD-Jones-ASES, six concyclic points).
The other Ramsey entries are on graph Ramsey problems.

**MathOverflow and Mathematics Stack Exchange** (Stack Exchange API, 01:20 UTC): "Euclidean
Ramsey" (5 and 3 hits, 2009 to 2024, none relevant), "Ramsey concyclic", "non-Ramsey heptagon" and
"Ramsey spherical set" (0 hits), "Ramsey points on a circle" (1 irrelevant hit on each site). The
erdosproblems.com forum thread for problem 174 (5 posts, the newest on 2026-09-23 about the
heptagon) does not discuss the class.

**Pálvölgyi's Theorem A.10**, reread: for a set on a circle that a Möbius map sends to algebraic
points apart from at most three, his derivation certificates for non-Ramsey-ness do not exist. It
draws no Ramsey conclusion for the class, which is what Theorem B(b), with Theorem C of
mobius-ramsey, supplies.

**Not searched:** the full text of PDFs, Lean Zulip, Google Scholar, zbMATH and OpenAlex (the
last two were searched in the earlier sweeps). GitHub code search is incomplete.

## Nearest work found

- **OpenAI, result 172**: the classification, its field criterion and sufficiency theorem (the
  foundation), and the circle results above.
- **The six-point case** (JD-Jones-ASES) and **the case `T` empty** (JD-Jones-ASES,
  Rogerhu12, atimics) are prior work, credited in `README.md`.
- **Pálvölgyi, arXiv:2609.23327**: the non-Ramsey heptagon, and Theorems A.3 (three cannot be
  replaced by four) and A.10 (above).

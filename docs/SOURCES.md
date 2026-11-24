# Sources and copyright

## The text
- **Lewis Carroll** (Charles Lutwidge Dodgson, 1832–1898), *Curiosa Mathematica, Part II: Pillow-Problems thought out during wakeful hours*, fourth edition, Macmillan & Co., London, 1895. The first edition appeared in 1893.
- Digital edition: **Project Gutenberg eBook #79080**, released 28 July 2026 and produced by the Online Distributed Proofreading Team at <https://www.pgdp.net>.
  - Catalogue page: <https://www.gutenberg.org/ebooks/79080>
  - Source used here: the MathJax HTML source, `79080-src/79080-src.htm`. It keeps the mathematics as TeX.

## Copyright status
| Jurisdiction | Rule | Status |
|---|---|---|
| United States | published before 1931 | public domain (published 1895) |
| India | author's life + 60 years | public domain since 1959 (Carroll d. 1898) |
| EU / UK | author's life + 70 years | public domain since 1969 |

**How the text is used:**
- Quotations in the Lean files and in `data/problems.json` reproduce the public-domain 1895 text.
- None of the Project Gutenberg licence boilerplate or trademark is reproduced.

## How the quotations were produced
- `scripts/extract_source.py` reads the Gutenberg source and writes `data/problems.json`. For each of the 72 problems it records:
  - the question (Chapter I), with the date Carroll noted where he gave one;
  - his separate answer (Chapter II), for the 44 problems that have one;
  - his full solution (Chapter III);
  - his subject classification, from the book's "Subjects classified" index.
- Mathematics stays as TeX (`\( … \)`), emphasis becomes `*…*`, and figures are replaced by their alt-text descriptions from the Gutenberg edition.
- `scripts/make_skeletons.py` turns each problem into `PillowProblems/PNN.lean`, quoting the question and the answer verbatim.

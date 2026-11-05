# Review checklist for an exposition chapter

You are an independent reviewer: you did not write the chapter. Read `STYLE.md` first. Work from
the scanned book pages (`pages/p-NN.png`, two book pages per image, book page `b` on image
`p-(floor(b/2)+3)` give or take one), not from memory of the book.

1. **Coverage.** List every numbered definition, lemma, theorem, corollary, remark and example on
   Milnor's pages for the chapter. Each must appear in the chapter with the right number and a
   statement equivalent to Milnor's, or stronger with the difference said explicitly.
2. **Proofs.** Read every proof line by line. Each must be complete and correct, with no "clearly"
   left unjustified. Check every computation, by hand or with a short `python3` script (numpy and
   sympy are available). Fix errors in place.
3. **Faithfulness.** Every claim about what Milnor wrote — page numbers, quotations, "Milnor's
   text skips …", "a hidden hypothesis", corrections of misprints — must match the scan. Remove or
   correct any that do not. Quotations of the book are at most a short phrase each; replace longer
   verbatim passages by paraphrase (the book is under copyright).
4. **Applications and numbers.** Every physical or numerical claim in the opening question and in
   the application section must be standard and correct. Recompute numbers; remove anything that
   cannot be verified.
5. **Companion volume.** Each citation "Chapter k of the companion volume" must point to the chapter
   of `../Exposition/` that actually
   contains the result (grep it). Results cited from there must be stated precisely.
6. **Figure.** The `.py` runs and writes the `.png`; the `.js` passes `node --check`; the prose
   describing the figure matches what the figure shows.
7. **Build.** `python3 build.py N` (from `Exposition/`) produces the PDF and the web page without
   errors.

Edit the chapter in place to fix what you find; keep the author's structure and voice, and make
changes minimal and precise. Do not touch other chapters.

Final report (≤ 250 words): the coverage list (one line, numbers only), the list of changes made
(one line each), and anything you could not resolve.

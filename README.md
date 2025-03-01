# Monsky's Theorem

Contributors (in alphabetical order): Dhyan Aranha, Pjotr Buys, Malvin Gattinger, Giacomo Grevink, Jan Hendriks, Thomas Koopman, Dion Leijnse, Thijs Maessen, Maris Ozols, Jonas van der Schaaf, Lenny Taelman

In this fork of Moritz Firsching's [project](https://github.com/mo271/FormalBook) to formalize [Proofs from THE BOOK](https://link.springer.com/book/10.1007/978-3-662-57265-8) using [Lean4](https://leanprover.github.io/lean4/doc/whatIsLean.html), we take up the job of formalizing Monsky's Theorem, Chapter 22: 

Theorem (Monsky) : It is not possible to dissect a square into an odd number of triangles of equal area. 

We also formalize and prove the theorem that it is always possible to do this with an even number of triangles of equal area. 

Theorem: It is always possible to dissect a square into an even number of triangles of equal area.

(This was carried out by Pjotr Buys in [Monsky_even](https://github.com/dhyan-aranha/FormalBook/tree/main/FormalBook/sperner))

Below is a summary of our work, and in which files it is included in this repository. 

1) In [Appendix.lean](https://github.com/dhyan-aranha/FormalBook/blob/main/FormalBook/Appendix.lean),
   it is shown that the real numbers admit a non-Archimedean valuation: v, with values in an orderd abelian group such that,
   v(1/2) > 1.

2) In [Rainbow_triangles.lean](https://github.com/dhyan-aranha/FormalBook/blob/main/FormalBook/sperner/Rainbow_triangles.lean)
   using the valuation from 1) we construct a tri-coloring of the unit square S in R^2. We use this coloring to define the notion of
   ***rainbow triangle***: a triangle whose vertices consist of three different colors. We also prove various properties about this coloring.
   Two important ones are: i) Any line in S containes at most two colors, ii) The area of a rainbow triangle cannot be 0 and it cannot be 1/n
   for n odd.

3) In the [Sperner file](https://github.com/dhyan-aranha/FormalBook/tree/main/FormalBook/sperner) the proof Monsky's theorem is carried out (see  [segment_conting.lean](https://github.com/dhyan-aranha/FormalBook/blob/main/FormalBook/sperner/segment_counting.lean)) as well
  as the proof that even dissections always exist. This is by far the most technincal part of the work.  There are still a few sorrys in here which we hope to fill soon. Also, here would like to recognize
  the contributions of Pjotr Buys!

4) Finally in [Triangle_corollary.lean](https://github.com/dhyan-aranha/FormalBook/blob/main/FormalBook/Triangle_corollary.lean) we formalize the comparison
   between the area of a triangle in R^2 given by measure theorem and the formula given in terms of the determinant.

While this is our working repository, one can find a repository which just contains our files (and not the other files in the fork) here : https://github.com/dhyan-aranha/Monsky. Below you will find the original ReadMe.

# Formal BOOK

> 🚀 **Pull Requests Welcome!** 🎉
> 
> We warmly welcome contributions from everyone.
> No experience is necessary, and partial proofs help with LaTex are appreciated!


A collaborative, work-in-progress attempt to formalize [Proofs from THE BOOK](https://link.springer.com/book/10.1007/978-3-662-57265-8) using [Lean4](https://leanprover.github.io/lean4/doc/whatIsLean.html).


![Formal Proofs from THE BOOK](formal_proofs_form_the_book.svg)

## Structure

For each chapter in the book (we follow the latest, sixth edition), there is a lean source file containing as many formalized definitions, lemmas, theorems and proofs as we can reasonably currently formalize using [Lean's mathlib4](https://github.com/leanprover-community/mathlib4).

The goal is to make the formalizations of the proofs as close as possible to the proofs in the book, even if a different proof for a theorem might already be present in mathlib or is more suitable for formalization.

We follow the [naming conventions](https://github.com/leanprover-community/mathlib4/wiki/Porting-wiki#naming-convention) and [code style](https://leanprover-community.github.io/contribute/style.html) of mathlib4.

## Blueprint

Checkout the [project's blueprint](https://firsching.ch/FormalBook)!

## Installation

This project uses Lean 4. You first need to [install elan and lean](https://leanprover.github.io/lean4/doc/setup.html) and then run
```shell
lake exe cache get
lake build
code .
```

The last step only opens vscode in case you want to use that.

## Contributing

Contributions are most welcome! Feel free to
  - grab a chapter that is not yet formalized and formalize
    - definitions, (if not yet in mathlib)
    - statements and
    - proofs
  - partial proofs with new `sorry` are also great!
  - fill in [`sorry`s](https://github.com/search?q=repo%3Amo271%2FFormalBook+sorry+path%3A*.lean&type=code) in lean files
  - fill in ['TODO's](https://github.com/search?q=repo%3Amo271%2FFormalBook+TODO+path%3A*.tex&type=code) in LaTeX files in the [blueprint](https://firsching.ch/FormalBook)
  - suggest improvements to proofs/code golf
  - correct typos/formatting/linting

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

## Authors

A list of contributors can be found here: [AUTHORS](AUTHORS.md)
or look at the [github stats](https://github.com/mo271/FormalBook/graphs/contributors).


Some contributions come the repo
[FordUniver/thebook.lean](https://github.com/FordUniver/thebook.lean),
which also has a nice [blog](https://thebook.zib.de/) on the proofs formalized there.


## License

Apache 2.0; see [`LICENSE`](LICENSE) for details.

## Disclaimer

This project is not an official Google project. It is not supported by
Google and Google specifically disclaims all warranties as to its quality,
merchantability, or fitness for a particular purpose.

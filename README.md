Going through [Programming Language Foundations in Agda](https://plfa.github.io/).

This requires the `Agda` [standard-library](https://github.com/agda/agda-stdlib) to run.

## Differences with the book

Some things are different due to either preference or what unicode I have "easily available" (due to using [agda-vim](https://github.com/derekelkins/agda-vim)).

* Various {sub,super}scripts are renamed, for ease of typing.
* `_≲_` from `plfa.Isomorphism` is `_≼_` instead (easier to type, already accessible from `agda-vim` )
* `to∘from` and `from∘to` from `_≃_` have an implicit instead of explicit argument, it seems more natural
* `⊥-elim` from `plfa.Connectives` is `efq` because it's semantically more meaningful
* `em` from `plfa.Negation` is `lem` because I'm used to that name more
* `iff` from `plfa.Decidable` is `_⇔b_`; `iff-⇔` is `⇔b-⇔`
* `map-++-commute` from `plfa.Lists` is `map-homomorphic-++`

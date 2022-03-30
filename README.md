# Herbrand's unification theorem for flows

This repo contains (at the moment) a proof of Herbrand's [1] unification theorem [2] for flows [3] [4].

I am interested in formalizing *flows* [3] [4], which are object that allow to present low-level computations in a satisfactory way (up to my understanding).
The first step towards this goal is the theorem that I proved here.

The project is more of a speedrun of the theorem at the moment. It took me about two weeks (I'd say I spend 50% of my time on the actual theorem and the other 50% on groundwork).

Now that the theorem is proven, there is some cleaning to do in the files (to make them look less speedrun-y...):

 * Split and reorganize the files
 * Automate the proof !
 * Extract the computational part from the theorem (I want to be able to automatically get a unifier)
 * Commit to [mathlib4](https://github.com/leanprover-community/mathlib4) ?

## Development

I am working on making properties decidable (the goal is to prove equalities of flow multiplications by `decide` or by a simple tactic).

At the moment, the inclusion on `Fintype` is decidable:
```lean
example : 0 ∈ (𝒱 (Term.Cons (Term.Var 0) (Term.Var 1) : Term Nat Nat) : Fintype Nat) := by
  decide
```

## References

[1] : Lectures on Herbrand, with historical notes https://arxiv.org/pdf/0902.4682.pdf

[2] : Jacques Herbrand's [dissertation](http://www.numdam.org/item/THESE_1930__110__1_0.pdf) (in French), pp. 96-97

[3] : Geometry of Interaction analyzed with flows https://www.normalesup.org/~bagnol/notes/goi-torino.pdf

[4] : Notes on unification using flows (in French) https://www.normalesup.org/~bagnol/notes/unification.pdf (in French)

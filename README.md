# vitrea
A tiny implementation of lenses and optics in Agda.  The formal proofs that
derive the concrete representations from the existential representations become
the isomorphisms that translate between them.

``` agda
-- We derive lenses from their existential representation.
lensDerivation {s} {t} {a} {b} =
  begin
   ((∫exists c ∈ Set , ((s -> c × a) × (c × b -> t))))           ≅⟨ ≅-coend (λ c -> trivial) ⟩
   ((∫exists c ∈ Set , (((s -> c) × (s -> a)) × (c × b -> t))))  ≅⟨ ≅-coend (λ c -> trivial) ⟩
   ((∫exists c ∈ Set , ((s -> c) × (s -> a) × (c × b -> t))))    ≅⟨ yoneda ⟩
   ((s -> a) × (s × b -> t))
  qed
```

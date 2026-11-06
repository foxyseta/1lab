---
description: |
  We show that the universe of n-types is not an n-type for n equal to
  -1, 0 or 1.
---
<!--
```agda
open import 1Lab.Prelude

open import Data.Bool

open import Homotopy.Space.Circle
```
-->

```agda
module 1Lab.Counterexamples.HLevel.Universe where
```

# Univalent universes of $n$-types are not $n$-types

Recall that, as we have observed when discussing [[universes of
$n$-types]], the univalent universe of $n$-types of some level is an
$(n + 1)$-type. For $n = -2$, we can actually improve on this
bound: the univalent universe of [[contractible]] types is itself
contractible.

```agda
Contr-is-contr : ∀ {ℓ} → is-contr (Contr ℓ)
Contr-is-contr .centre = el! (Lift _ ⊤)
Contr-is-contr .paths = hlevel!
```

However, $-2$ is the only value of $n$ for which this holds. In general,
the univalent universe of $n$-types is a proper $(n + 1)$-type. On this
page, we prove this for $n \in \{-1,0,1\}$.

## The univalent universe of propositions is not a proposition

If the univalent universe of propositions were a [[proposition]], we
would have a [[path]] from `⊤`{.Agda} to `⊥`{.Agda}, which we could use
to turn a proof of `⊤`{.Agda} into a contradiction.

```agda
¬Prop-is-prop : ∀ {ℓ} → ¬ is-prop (Prop ℓ)
¬Prop-is-prop {ℓ} Prop-is-prop =
  let
    Lift-⊤≡Lift-⊥ = Prop-is-prop (el! $ Lift ℓ ⊤) (el! $ Lift ℓ ⊥)
  in lower (subst ∣_∣ Lift-⊤≡Lift-⊥ _)
```

## The univalent universe of sets is not a set

In example 3.1.9, the HoTT book [-@HoTT] uses `Bool`{.Agda}, the type of
[[booleans]], to show that [[univalence]] implies that the bottom level
universe of all types is not a [[set]]. This way, one observes that
univalence truly bestows higher structure upon the type universe.
Because `Bool`{.Agda} is, in particular, a set itself, we can reuse the
same proof strategy to show that not even the univalent universe of
sets is a set.

Since `true`{.Agda} and `false`{.Agda} are distinct, so are the two
[[equivalences]] on `Bool`{.Agda} given by the identity
function and negation respectively.

<!--
```agda
_ = false
```
-->

```agda
private
  id≠not : id≃ ≠ not≃
  id≠not = true≠false ∘ _·ₚ true
```

We now assume the univalent universe of sets to also be a set, aiming
for a contradiction. By definition of set, the path type from
`Bool`{.Agda} to itself would be a proposition. Now, in such a
universe, univalence guarantees this path type to be equivalent to the
type of equivalences on `Bool`{.Agda}. Because homotopy levels are
preserved by equivalences, the type of equivalances from `Bool`{.Agda}
to itself would then also be a proposition. We would therefore have a
path from the identity to negation. This contradicts our previous
observation.

```agda
  ¬Set₀-is-set : ¬ is-set (Set lzero)
  ¬Set₀-is-set Set-is-set = id≠not $
    Equiv→is-hlevel 1 n-univalence (Set-is-set (el! Bool) (el! Bool)) id≃ not≃
```

To generalise our proof from `Set lzero`{.Agda} to `Set`{.Agda} at an
arbitrary universe level $\ell$, we recall that `n-Lift`{.Agda} provides
an embedding between the two (see `n-Lift-is-embedding`{.Agda}), and
that embeddings reflects homotopy levels by
`embedding→is-hlevel`{.Agda}.

<!--
```agda
_ = n-Lift
```
-->

```agda
¬Set-is-set : ∀ {ℓ} → ¬ is-set (Set ℓ)
¬Set-is-set = ¬Set₀-is-set ∘ embedding→is-hlevel 1 (n-Lift-is-embedding 2 _)
```

We also prove the weaker statement from example 3.1.9 in the HoTT book
[-@HoTT], which only concerns the type universe.

```agda
¬Type-is-set : ∀ {ℓ} → ¬ is-set (Type ℓ)
¬Type-is-set h = ¬Set-is-set (embedding→is-hlevel 1 ∣-∣-is-embedding h)
```

## The univalent universe of groupoids is not a groupoid

To prove that the univalent universe of [[groupoids]] is not a
groupoid, we replace `Bool`{.Agda} from the proof above with
`S¹`{.Agda}, the [[circle]].

The crux of the previous proof was showing that there is more than one
equivalence on `Bool`{.Agda}, i.e. the type of equivalences on
`Bool`{.Agda} is not a proposition. Similarly, we will now need to prove
that the type of equivalences on `S¹`{.Agda} is not a set.

We start by upgrading `always-loop`{.Agda} to a loop around the identity on
`S¹`{.Agda} regarded as an [[equivalence]].

```agda
private
  id≃-loop : id≃ {A = S¹} ≡ id≃
  id≃-loop = Σ-prop-path is-equiv-is-prop (funext always-loop)
```

We now prove `id≃-loop`{.Agda} to be distinct from `refl`. If the two
were equal, moving to the first component of the $\Sigma$-type
`_≃_`{.Agda} and then to homotopies, `always-loop`{.Agda} would
coincide with `id`{.Agda}. In particular, by evaluating both functions
at `base`{.Agda}, we would contradict `never-refl`{.Agda}. So
`id≃-loop`{.Agda} must be distinct from `refl`{.Agda}.

```agda
  refl≠id≃-loop : id≃-loop ≠ refl
  refl≠id≃-loop id≃-loop≡refl =
    let
      base-path p = happly p base
      refl-at-base = ap (base-path ∘ fst ∘ fst (Equiv.inverse Σ-pathp≃))
        id≃-loop≡refl
    in never-refl base refl-at-base
```

We can now use the circle to refute the idea that the univalent universe
of all groupoids is a groupoid. Assume it is. Then, in particular, the
loop space on `S¹`{.Agda} would be a set. By univalence for homotopy
sets, and because equivalences respect homotopy levels, so would the
type of equivalences on `S¹`{.Agda}. In particular, the loop space on
the equivalence on `S¹`{.Agda} given by the identity would be a
proposition. Thus, `id≃-loop`{.Agda} would have to coincide with `refl`{.Agda}.
This contradicts our observation above.

```agda
  ¬Groupoid₀-is-groupoid : ¬ is-groupoid (Groupoid lzero)
  ¬Groupoid₀-is-groupoid Groupoid₀-is-groupoid =
    let
      S¹≃S¹-is-set = Equiv→is-hlevel 2 n-univalence $
        Groupoid₀-is-groupoid (el! S¹) (el! S¹)
      id≃≡id≃-is-prop = S¹≃S¹-is-set id≃ id≃
    in refl≠id≃-loop $ id≃≡id≃-is-prop id≃-loop refl
```

We use the same argument as before to generalize to an arbitrary
universe.

```agda
¬Groupoid-is-groupoid : ∀ {ℓ} → ¬ is-groupoid (Groupoid ℓ)
¬Groupoid-is-groupoid = ¬Groupoid₀-is-groupoid ∘
  embedding→is-hlevel 2 (n-Lift-is-embedding 3 _)
```

### Necessity of higher inductive types

On top of [[univalence]], this last proof makes use of a higher
inductive type. In the absence of these, Kraus and Sattler
[-@KrausSattler:higher, §6] explain that it is possible to construct a model where,
for every $n \geq 0$, every type in the universe at level $n$ is
$n$-truncated. As a consequence, the bottom universe would then be a
groupoid, and so would `Groupoid lzero`.

Proving that the universe of $n$-types is not $n$-truncated for higher
values of $n$ could be done using a similar strategy via Eilenberg–MacLane spaces;
see [this MathOverflow question](https://mathoverflow.net/questions/222914).

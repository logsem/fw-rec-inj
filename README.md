## Prerequisites
- coq 8.16.1

## Installation
- with [nix](https://nixos.org/download.html):
  ```
  nix-shell
  ```
- with [opam](https://opam.ocaml.org/doc/Install.html):
  ```
  opam pin add coq 8.16.1
  eval $(opam env)
  ```
- with [docker](https://docs.docker.com/engine/install/):
  ```
  docker build -t artifact .
  docker run --rm -it --entrypoint /bin/bash artifact
  eval $(opam env)
  ```
- alternatively, you can install it with a package manager of your choice

## Typechecking the development
- ```make all``` --- typecheck the project.
- ```./check_admits.sh``` --- count used admits.
- ```./check_axioms.sh``` --- count declared axioms.

## Cleanup
- ```make clean``` --- remove generated build files.
- ```make cleanfull``` --- remove Coq bytecode files.

## Mapping the paper onto the development

In this section, we walk through the main claims of the paper, section
by section, and refer to the appropriate definitions/theorems in the
Coq formalisation, as well as explain some representation choices and
formalisation decisions. The inverse mapping (in the form of
annotations for the particular files of the project) and a glossary of
names used in the paper/formalisation may be helpful, and can be found
below.

### Section 2, definition of the calculus

The definition of the calculus can be found in the `Lang/FOmegaEq`
subdirectory of the projects, in the files `Kinds.v`, `Types.v`,
`Syntax.v`, `Typing.v` and `OpSemantics.v`. The syntax of kinds and
type constructors (Fig. 1 in the paper) is defined in the file
`Kinds.v` as inductive families `kind` and `tctor` respectively; note
that we represent type-constructors as intrinsically well-kinded (thus
incorporating part of Fig. 2). The syntax of types and constraints
(the remainder of Fig. 1) is defined in the file `Types.v` as the
mutually inductive families `type` and `constr`; as with the type
constructors these are intrinsically well-kinded (or well-formed in
the case of constraints; thus, they incorporate the remainder of
Fig. 2). This design choice is rather helpful in the remainder of
formalisation, as it incorporates additional information (e.g., about
the type of argument in type-level beta redexes) that allows for
building the interpretation by induction on the structure of the
type. At the same type (in contrast to well-behaved but ill-typed
programs), ill-kinded types are not practically useful, so we do not
lose any important information.

The discriminability and provability of equality constraints (Fig. 3)
judgments are also defined in the file `Types.v` (as inductive
judgments `tdiscr` and `tproves_i`, respectively), together with a
number of lemmas (closure under renaming/substitution, weakening, cut
admissibility).

The term-level syntax of the calculus (Fig. 4), comprising values and
expressions, is defined in the file `Syntax.v` as the mutually
inductive types `value` and `expr`. These are intrinsically
well-scoped, but untyped. Instead of defining evaluation contexts
explicitly, together with a reduction semantics (Fig. 6) we define a
structural operational semantics, as the judgment `head_step` (for a
single-step relation), found in the file `OpSemantics.v`. Particularly
for a fine-grain call-by-value, equivalence of the two formats is
trivial.

Finally, the type system (Fig. 5) is presented in the file `Typing.v`,
as the mutually inductive predicates `typing_expr` and `typing_val`
(respectively for typing of expressions and values). The file also
provides numerous lemmas (closure under renaming/substitution, both
with respect to type- and term-level variables, as well as weakening
and cut lemmas for the equality assumptions).

The example of a closed value of the empty type can be found in the
final section of the file `Typing.v`, with the final lemma, `tnt`,
building a proof that the constructed value has indeed type `void`.
Since the simpler sub-calculus without recursive types and injectivity
of quantifiers is only explicitly used in the (un-formalised) Theorem
3.2, we do not provide this variant explicitly. We also do not provide
the encodings of examples of GADTs found in Section 2.1.

### Section 3, non-expressibility of injective constraints

The formalised part of this section comprises the propositional model
of Fω, and can be found in the subdirectory `Lang/FOmega`. The
calculus is structured similarly to the larger system and is split
across three files: the file `Types.v` provides the structure of
kinds, (intrinsically well-kinded) types and type equality, while the
file `Syntax.v` provides the term-level syntax of the calculus. The
file `Interp.v` provides the propositional interpretation of the
calculus, written `tint`, as defined in Fig. 11 in the paper. Note
that we work in the category of setoids and equality-preserving
arrows, in order to construct the interpretation together with the
proof that it preserves equality of contexts. While other options are
available (e.g., assuming functional extensionality), this
construction is more in keeping with the NbE interpretation presented
in Section 5, which relies on a similar approach (in a more
complicated setting) to build functoriality into the
construction. Theorem 3.1, which ensures that the truth of the
interpretation of a type follows from the truth of the interpretation
of the context is located at the end of the file `Interp.v`, under the
name of `etypes_true`. As noted in the paper, Theorem 3.2 is left
un-mechanised, since its proof is simple and provided in the paper,
while a mechanisation would be rather convoluted.

### Section 4, type-soundness of the calculus

The syntactic proof of type-soundness can be found in the file
`Soundness.v` in the subdirectory `Lang/FOmegaEq` of the
development. While it depends on our NbE interpretation, we defer its
discussion till the next section; note only that the Lemma 4.1
(Consistency), on which the remainder of this section depends, can be
found at the end of the file `Interp.v`. From there, we proceed via a
series of canonical-forms lemmas for particular type constructors,
through the usual formulations of the `progress` and `preservation`
lemmas, up to the final `soundness` theorem stating that well-typed
programs are `safe` (def'n in `OpSemantics.v`, above). Note that,
while that definition is not identical to the paper, it is equivalent,
since irreducibility is trivially decidable.

### Section 5, NbE and relational models

The structure of the formalisation of this section differs slightly
from the paper. This is because, in order not to duplicate the
formalisation effort, the NbE procedures used in Sections 5.2 and 5.3
are joined together, with a type of "open universes" (Fig. 18), found
in the functor `NF` in the file `Universe.v` *parameterised* by the
type of predicates. Taking this parameter to be empty we regain the
usual neutral and normal forms (Fig 12.), while taking it to be
step-indexed relations on values gives us the open universes we use in
Section 5.3. The other ingredient necessary for our implementation of
the NbE algorithm is the notion of presheaves, and in particular of
the exponential presheaf: these can be found in the file
`Presheaves.v`. Note that, although we use these notions and concepts,
we cannot fully utilise the internal language of presheaves within
Coq; we will point out the discrepancies in the following. The
interpretation of kinds (Definition 5.2, written `kint` in the
formalisation), as well as its point-wise extension to contexts and
proofs that the universes form presheaves can be found in the file
`Universe.v`, after the inductive universes are defined.

We can now move on to the actual normalisation procedure, which is
defined in the file `Interp.v`. The reflection and reification
functions (Fig. 13) are defined by mutual induction on the structure
of the kind `reflectI` and `reifyI`, respectively. For practical
reasons, rather than at an arbitrary index, we define them at the
empty indexing context (picking an indexing context is necessary,
since the type of the exponential presheaf `PArr (PNeu κ) (kint κ)` is
*not* a Coq universe, but a type of universe-valued functions). This
does not prevent us from using the functions at other indexes,
however: the wrappers `reify` and `reflect` provide the mappings as
Coq functions at the arbitrary index. The interpretation of types and
constraints (Fig. 14) follows the same pattern, with functions `tint`
and `constrint` building an instance of the appropriate presheaf, and
wrappers `interp` and `interpC` used for practical convenience. We
also define the identity environment (Def. 5.3) as `η_id`.

Since the universes we use allow for non-syntactic elements (like
step-indexed relations over values), we replay the interpretation for
the universes (as discussed in Section 5.3): this re-interpretation is
defined as the three functions `neuint`, `nfint` and `nfconstrint`,
which interpret neutral universes, normal universes and normal
constraints back into the appropriate semantics spaces.

With these definitions, we can define the logical relation (Fig. 15),
which is written `sub_rel` in the development and precisely matches
the paper definition, and its extension to environments, written
`sub_relS`. With these two, we can prove the necessary lemmas: Lemma
5.5 corresponds to `interp_reify`, Lemma 5.6 — to `interp_rel` and
Lemma 5.4 — to `reify_refl_inj`. Finally, Lemma 5.7, which expresses
validity of provability and discriminability judgment corresponds to
`tproves_int` (for provability) and `tdiscr_int` (for
discriminability) — and together, they imply the consistency lemma of
the previous section. Before the elements of the universe are realized
as predicates/relations, we provide a more convenient representation
for its closed, ground fragment in the file `GroundView.v`.

At this point, the development forks into two branches, corresponding
to the simpler, unary realization of Section 5.2, and the more
sophisticated binary realization of Section 5.3. The first can be
found in the subdirectory `Lang/FOmegaEq/Unary`. The definition of
realization (Fig. 16) can be found in the file `Realize.v` in that
directory, with the evaluation closure written `ECL`, and the
realization (defined as a guarded fixpoint via a step-indexed logic
library) written `RP`. The logical relation (Fig. 17) corresponds to
definitions `logrelE` and `logrelV` for the versions for expressions
and values, respectively. This leaves us with the compatibility lemmas
and fundamental theorem, found in the file `Compat.v`, and its
corollary, semantic proof of soundness, found in the file `Soundness.v`.

As already mentioned, the binary model follows the same pattern,
although with a slightly more sophisticated universe of normal
forms. However, this has little bearing on realization: the definition
is very similar, with the only difference stemming from the usual
asymmetry of a step-indexed binary model. The files can be found in
the `Lang/FOmegaEq/Binary` subdirectory, with the realization defined
in the file `Realize.v`, compatibility and fundamental lemma in the
file `Compat.v`, contextual approximation and adequacy in the file
`Soundess.v`, and the examples in the file `Examples.v`.

## Project layout
```
.
+-- README
+-- Makefile
+-- _CoqProject
+-- Binding/ (substitution framework)
+-- IxFree/ (step-indexed logic framework)
+-- Lang/
|   +-- FOmega/ (propositional model of Fω)
|   +-- FOmegaEq/Kinds.v (syntax for kinds, syntax for type constructors with their corresponding kinds)
|   +-- FOmegaEq/Types.v (intrinsicly well-kinded types, discriminability and provability rules, renaming and substitution lemmas for kinding, cut lemma for provability)
|   +-- FOmegaEq/Syntax.v (syntax for well-scoped expressions and values, renaming and substitution functions)
|   +-- FOmegaEq/Typing.v (typing of expressions and values, renaming and substitution lemmas for typing, non-terminating example, derived using injectivity of forall)
|   +-- FOmegaEq/OpSemantics.v (operational semantics, safety definition, reflexive-transitive closure, n-step relation)
|   +-- FOmegaEq/Presheaves.v (presheaves, presheaf exponential)
|   +-- FOmegaEq/Universe.v (inductively defined universe of extended normal and neutral forms, presheaf structure of Nf k and Neu k)
|   +-- FOmegaEq/Interp.v (reflect, reify and eval for NbE, injectivity of reify)
|   +-- FOmegaEq/GroundView.v (closed ground types)
|   +-- FOmegaEq/Soundness.v (syntactic soundness)
|   +-- FOmegaEq/Unary/ (unary realizability model)
|   |   +-- Realize.v
|   |   +-- Compat.v
|   |   +-- Soundness.v
|   |   +-- SoundnessNbE.v (proof of soundness for NbE)
|   +-- FOmegaEq/UnaryPredicate (unary realizability model with predicates)
|   |   +-- Realize.v
|   |   +-- Compat.v
|   |   +-- Soundness.v
|   |   +-- Examples.v
|   +-- FOmegaEq/Binary/ (binary model)
|   |   +-- Realize.v
|   |   +-- Compat.v
|   |   +-- Soundness.v
|   |   +-- Examples.v
```

## Paper-formalization glossary
| Paper entry | Coq qualified identifier |
| ----------- | -------------- |
| fig. 1 (kinds) | ```Kinds.kind``` |
| fig. 2 (well-kinded constructors) | ```Kinds.tctor``` |
| fig. 1 (types) | ```Types.type``` |
| fig. 2 (well-kinded types) | ```Types.type``` |
| fig. 3 (provability, discriminability, auxiliary lemmas) | ```Types.tdiscr```, ```Types.tproves_i``` |
| fig. 4 (values, expressions, evaluation context, auxiliary lemmas) | ```Syntax.value```, ```Syntax.expr``` |
| fig. 5 (type system) | ```Typing.typing_expr```, ```Typing.typing_val``` |
| non-termination paragraph in sec. 2 | ```Typing.ExampleClosedVoid``` |
| fig. 6 (operational semantics) | ```OpSemantics.head_step``` |
| Auxiliary definitions for presheaves in sec. 5 (used for def. 5.1, and for computations taking place in Pr(K)) | ```Presheaves.Functors```, ```Presheaves.Arrows``` |
| fig. 12 | Module ```Universe.NF```, in particular ```neu```, ```nf```, ```nfc``` (note, that it's already has an additional constructor that is introduced in fig. 18, but if the module is instantiated with ```False```, then the definition matches the one in the fig. 12) |
| fig. 18 | Module ```Universe.NF```, in particular ```neu```, ```nf```, ```nfc```, if instantiated with ```val ∅ -> val ∅ -> iProp``` |
| def. 5.2 | ```Universe.NF.kint``` |
| lemma 4.1 | ```Interp.Interp.consistency``` |
| lemma 5.4 | ```Interp.Interp.reify_refl_inj```, ```Interp.Interp.reify_refl_inj'``` |
| lemma 5.5 | ```Interp.Interp.reinterp_nf``` |
| lemma 5.6 | ```Interp.Interp.interp_rel``` |
| lemma 5.7 | ```Interp.Interp.tproves_int```, ```Interp.Interp.tdiscr_int``` |
| def. 5.3 | ```Interp.Interp.η_id``` |
| fig. 13 | ```Interp.Interp.reifyI```, ```Interp.Interp.reflectI``` |
| fig. 14 | ```Interp.Interp.tint``` |
| fig. 15 | ```Interp.Interp.sub_rel``` |
| lemma 4.2 | ```Soundness.canArr``` |
| lemma 4.3 | ```Soundness.preservation``` |
| lemma 4.4 | ```Soundness.progress``` |
| lemma 4.6 | ```Soundness.soundness``` |
| def. 4.5 | ```Soundness.safety``` |
| fig. 16 | ```Unary.Realize.RPR```, ```Unary.Realize.RP``` |
| fig. 17 | ```Unary.Realize.logrelV```, ```Unary.Realize.logrelE``` |
| theorem 5.8 | ```Unary.Compat.fl_expr```, ```Unary.Compat.fl_val``` |
| fig. 19 | ```Binary.Realize.RPR```, ```Binary.Realize.RP``` |
| Representation independence example from sec. 5.3 | ```Binary.Examples.Vec``` |
| Free theorem example from sec. 5.3 | ```Binary.Examples.FreeThm``` |

## Notation glossary
### Substitution framework
|    | Paper | Coq formalization |
| -- | ----- | ----------------- |
| Renaming type | Δ → Δ' | ```Δ [→] Δ'``` |
| Substitution in terms | 𝑒 [𝑣/𝑥] | ```subst e v``` |
### Step-indexed framework
|    | Paper | Coq formalization |
| -- | ----- | ----------------- |
| Steped-indexed proposition | iProp | ```*ₛ``` |
| Step-indexed relation | | ```A →ₛ B``` |
| Embedding of intuitionistic logic into step-indexed logic | | ```( P )ᵢ``` |
| Step-indexed proposition P is valid at n | | ```n ⊨ P``` |
| Step-indexed proposition P is valid at any n | | ```⊨ P``` |
### FOmegaEq
|    | Paper | Coq formalization |
| -- | ----- | ----------------- |
| Discriminability | τ # σ | ```⊮ τ ≃ σ``` |
| Provability | Δ ∣ Ψ ⊩ τ ≡ σ | ```Ψ ⊩ τ ≃ σ``` |
| Kinding | Δ ⊢ τ :: κ | ```τ : typ κ Δ``` |
| Presheaf category on context renamings | Pr(K) | ```PShf``` |
| Presheaf exponential | ⇒ | ```PArr``` |
| Neutral forms | U♮, Neu | ```Neu``` |
| Normal forms | U, Nf | ```Nf``` |
| Kind interpretation | 〚κ〛 | ```kint κ``` |
| Context interpretation | 〚Δ〛 | ```NSub Δ``` |
| Type interpretation (first stage) | 〚τ〛 | ```tint τ``` |
| Good context interpretation | good(μ) | ```sub_rel η_id μ μ``` |
| Type interpretation (second stage) | R | ```RP``` |
| Evaluation closure | E | ```ECL``` |
## Tactic glossary
### Substitution framework
| Coq identifier | Explanation |
| -------------- | ----------- |
| ```term_simpl``` | move substitutions at the outermost level, move renamings at the intermost level, compose them, if possible, simplify |
### Step-indexed framework
| Coq identifier | Explanation |
| -------------- | ----------- |
| ```later_shift``` | eliminate ▷ in front of the goal, and all the hypothesis |
| ```i<tactic>``` | step-indexed counterparts of Coq tactics |

## Additional comments
- In our implementation, we use two styles of representation of terms with binders.
  Our types are intrinsicly well-kinded, parametrized over contexts and kinds:
  ```
  Inductive type {Δ : Ctx kind} : kind → Type :=
  | t_var κ (x : dom Δ) (EQ : Δ x = κ) : type κ
  | t_lam {κₐ κᵣ} (τ : @type (Δ ▹ κₐ) κᵣ) : type (κₐ ⇒ κᵣ)
  | t_app {κₐ κᵣ} (σ : type (κₐ ⇒ κᵣ)) (τ : type κₐ) : type κᵣ
  ...
  .
  ```
  Our expressions and values are well-scoped:
  ```
  Inductive value {V : Set} :=
  | v_lam (e : @expr (inc V)) : value
  ...
  with expr {V : Set} :=
  | e_bind (e₁ : expr) (e₂ : @expr (inc V)) : expr
  ...
  .
  ```
- We allow recursive types with arbitrary arity, but require them to be fully applied for programs. To enforce this condition with use the predicate ```Types.rel_app```.
- For the purpose of de-duplication, we implemented the first stage (denoted by 〚 〛 in the paper), for the unary and binary cases in one module, parametrized by a type, used as a parameter for the additional constructor. This type is given by signature ```Point``` (Universe.v):
  ```
  Module Type Point.
	  Parameter P : Type.
  End Point.
  ```
  ```
  Module NF (PM : Point).
	  Definition Point := PM.P.

	  Inductive neu {Δ : Ctx kind} : kind → Type :=
	  | neu_rel (P : Point) : neu ⋆
	  ...
	  with nf {Δ : Ctx kind} : kind → Type :=
	  ...
	  with nfc {Δ : Ctx kind} : Type :=
	  ...
	  .
  ```
  If ```Point.P := False```, and, hence, the set of normal/neutral types is a subset of types, we obtain a model for beta-short, eta-long types (used to prove syntactic soundness, and unary semantical soundness in the paper). If ```Point.P := val ∅ -> iProp```, we obtain a model that allows embedding of predicates for types at the base kind (used to construct a unary relational model), which is not used in the paper. If ```Point.P := val ∅ -> val ∅ -> iProp```, we obtain a model that allows embedding of relations for types at the base kind (used to construct a binary model in the paper).
- As for program-level reasoning it suffices to study their behavior at closed types at the base kind, and after NbE these types have a simplier structure (beta-short, eta-long), we can use ```gtyp``` (and ```viewG : Neu ⋆ ε -> gtyp```), defined in GroundView.v, to define realizability semantics.
- Unary/Example.v contains a trivial example of instantiating forall with a predicate to check a program with a presence of semantically correct (but probably syntactically not well-typed) expression.
- Unary/Soundness.v contains a proof that the unary logical relation implies safety (```adequacy```).
- Binary/Soundness.v contains a proof that the binary logical relation implies contextual approximation (```adequacy```).
- Binary/Compat.v contains a fundamental lemma for the binary logical relation.
- As any value of ```Point.P```, apart from ```False``` prevents the set of neutral and normal forms to be a subset of types, most lemmas in Interp.v require duplicate versions for types, for neutrals, and for normals.
- Soundness of the binary model is proved using Streicher's Axiom K.
- Syntax includes fixpoint combinator (v_fix) to shorten the examples.
- We disable the following warnings, which don't affect consistency of the mechanization: notation-overridden uniform-inheritance ambiguous-paths implicit-core-hint-db require-in-module unexpected-implicit-declaration undeclared-scope deprecated-hint-without-locality deprecated-instance-without-locality deprecated-syntactic-definition.

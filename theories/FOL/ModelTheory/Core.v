(* Basic definition in model theory *)

Require Export Undecidability.FOL.ModelTheory.ModelNotation.
Require Export Undecidability.FOL.Syntax.Theories.
Local Set Implicit Arguments.
(* Local Unset Strict Implicit. *)


Section Isomorphism.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Definition preserve_func {M N: model} (h: M -> N) := 
        forall func v,
            h (func ₕ[M] v) = func ₕ[N] (map h v).

    Definition preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            pred ₚ[M] v -> pred ₚ[N] (map h v).

    Definition strong_preserve_pred {M N: model} (h: M -> N) :=
        forall pred v,
            pred ₚ[M] v <-> pred ₚ[N] (map h v).

    Definition injective {M N} (f: M -> N) :=
        forall n m, f n = f m -> n = m.

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition bijective {M N} (f: M -> N) :=
        injective f /\ surjective f. 

    Class homomorphism {M N: model} (h: M -> N) :=
    {
        func_preserved : preserve_func h;
        pred_preserved : preserve_pred h;
    }.

    Class strong_homomorphism {M N: model} (h: M -> N) :=
    {
        homomorphism' :> homomorphism h;
        pred_strong_preserved : strong_preserve_pred h
    }.

    Class embedding {M N: model} (h: M -> N) :=
    {
        strong_homomorphism' :> strong_homomorphism h;
        morphism_injectived : injective h
    }.

    Class isomorphism {M N: model} (h: M -> N) :=
    {
        embedding' :> embedding h;
        morphism_surjective : surjective h 
    }.

    Definition isomorphic {M N: model} :=
        exists h: M -> N, isomorphism h.

    (* 
    Test the definition
    Goal forall (M N: model) (h: M -> N), isomorphism h -> embedding h.
    Proof.
        intros M N h iso.
        constructor. constructor. constructor.
        apply func_preserved.
        apply pred_preserved.
        apply pred_strong_preserved.
        apply morphism_injectived.
    Qed. 
    *)

End Isomorphism.

Section FunctionalRelation.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.

    Definition total_rel (X Y : Type) (R : X -> Y -> Prop) :=
        forall x, exists y, R x y.

    Definition functional_rel X Y (R : X -> Y -> Prop) :=
        forall x y y', R x y -> R x y' -> y = y'.

    Definition function_rel {X Y} (R: X -> Y -> Prop) := 
        functional_rel R /\ total_rel R. 

    Definition rev {X Y} (R: X -> Y -> Prop) x y := R y x.

    Definition injective_rel X Y (R : X -> Y -> Prop) :=
        functional_rel (rev R).

    Definition surjective_rel (X Y : Type) (R : X -> Y -> Prop) :=
        total_rel (rev R).

    Definition bijective_rel X Y (R : X -> Y -> Prop) :=
        function_rel R /\ function_rel (rev R).

    Inductive map_rel {X Y: Type} (R: X -> Y -> Prop): forall n: nat, vec X n -> vec Y n -> Prop :=
        | nil_rel: map_rel R (nil _) (nil _)
        | cons_rel n x y (vx: vec X n) (vy: vec Y n): 
            map_rel R vx vy -> R x y -> map_rel R (cons _ x n vx) (cons _ y n vy).

    Definition preserve_func_rel {M N: model} (R: M -> N -> Prop) := 
        forall func v, exists v',
            R (func ₕ[M] v) (func ₕ[N] v') /\ map_rel R v v'.

    Definition preserve_pred_rel {M N: model} (R: M -> N -> Prop) :=
        forall pred v, exists v',
            (pred ₚ[M] v <-> pred ₚ[N] v') /\ map_rel R v v'.

    Class isomorphism_rel {M N: model} (R: M -> N -> Prop) :=
        {
            func_preserved_rel: preserve_func_rel R;
            pred_preserved_rel: preserve_pred_rel R;
            morphism_biject_rel: bijective_rel R
        }.

End FunctionalRelation.


Section Elementary.
    Context {Σ_funcs : funcs_signature}.
    Context {Σ_preds : preds_signature}.
    Context {ff : falsity_flag}.

    Definition theory_of_model (M: model): theory :=
        fun φ => closed φ /\ M ⊨[_] φ.

    Fact closed_theory_of_model M: closed_T (theory_of_model M).
    Proof.
        now intros phi [closed sat].
    Qed.

    Definition elementary_equivalence M N :=
        forall phi, closed phi -> (M ⊨[_] phi) <-> (N ⊨[_] phi).

    Definition elementary_homomorphism {M N: model} (h: M -> N) :=
        forall phi ρ, M ⊨[ρ] phi <-> N ⊨[ρ >> h] phi.

End Elementary.


(* closed_theory_of_model : ∀ M: model, closed_T (theory_model M) *)
Arguments closed_theory_of_model {_ _ _} _.

Notation "M ≡ N"  := (elementary_equivalence M N) (at level 30).
Notation "M ≅ N"  := (exists h: M -> N, isomorphism h) (at level 30).
Notation "M ≅ᵣ N" := (exists R: M -> N -> Prop, isomorphism_rel R) (at level 30).
Notation "N ⪳ M"  := (exists h: N -> M, elementary_homomorphism h) (at level 30).
Notation "N ⪳[ h ] M"  := (@elementary_homomorphism _ _ _ N M h) (at level 30).

Section What_is_your_choice.

    Implicit Type (A: Type).

    Definition DP_on A (P: A -> Prop):=
        inhabited A -> 
            exists x, P x -> forall k, P k.

    Definition DP_ω_on A (P: A -> Prop) :=
        inhabited A -> 
            exists f: nat -> A, (forall n, P (f n)) -> forall k, P k.

    Definition NDP_ω_on A (P: A -> Prop) :=
        inhabited A -> 
            exists f: nat -> A, (forall n, ~ P (f n)) -> forall k, ~ P k.

    Definition SDP_ω_on' A (P: A -> Prop) :=
        inhabited A -> 
            exists f: nat -> A, (exists x, P x) -> (exists n, P (f n)).

    Definition SDP_ω_on A (P: A -> Prop) :=
        inhabited A -> 
            exists f: nat -> A, (exists x, P x) -> (forall n, P (f (S n))).

    Definition DC_on A (R: A -> A -> Prop) :=
        (forall x, exists y, R x y) ->
            forall w, exists f: nat -> A, f O = w /\ forall n, R (f n) (f (S n)).

    Definition CDC_on A (R: A -> A -> Prop) :=
        (forall x, exists y, R x y) ->
            forall w: A, exists f: nat -> nat -> A, 
                (forall b, f O b = w) /\  forall n m, exists k, R (f n m) (f (S n) k).

    Definition DC_weaker_on A (R: A -> A -> Prop) :=
        (forall x y, R x y \/ ~(R x y)) -> (forall x, exists y, R x y) ->
            forall w, exists f: nat -> A, f O = w /\ forall n, R (f n) (f (S n)).


    Definition ODC_on A (R: A -> A -> Prop) :=
        forall w,
            exists f : nat -> A, f 0 = w /\ forall n, (exists y, R (f n) y) -> R (f n) (f (S n)).

            Definition ODC_on' A (R: A -> A -> Prop) :=
                forall w,
                    exists f : nat -> A, f 0 = w /\ forall n, (forall m, R (f n) (f (S m))) -> (forall y, R (f n) y).

    Definition function_rel' {X Y} (P: X -> Y -> Prop) :=
        forall x, exists! y, P x y.

    Definition PDC_on A (R: A -> A -> Prop)  := 
        (forall x, exists y, R x y) -> forall w,
            exists P: nat -> A -> Prop, function_rel' P /\ P 0 w /\ forall n, exists x y,  P n x /\ P (S n) y /\ R x y. 

    Definition AC_on A B (R: A -> B->Prop) :=
        (forall n, exists y, R n y) -> exists f : A -> B, forall n, R n (f n).

    Definition CAC_on A B (R: A -> B -> Prop) :=
        (forall x, exists y, R x y) -> exists f: A -> (A -> B), 
            forall n, exists w, R n (f n w).

End What_is_your_choice.

Notation DP := (forall A P, @DP_on A P).
Notation DP_ω := (forall A P, @DP_ω_on A P).
Notation NDP_ω := (forall A P, @NDP_ω_on A P).
Notation SDP_ω := (forall A P, @SDP_ω_on A P).
Notation DC := (forall A R, @DC_on A R).
Notation ODC := (forall A R, @ODC_on A R).
Notation PDC := (forall A R, @PDC_on A R).
Notation AC := (forall A B R, @AC_on A B R).
Notation AC_ω := (forall A R, @AC_on nat A R).
Notation AC_form := (forall A R, @AC_on form A R).
Notation CAC_ω := (forall A R, @CAC_on nat A R).

Notation ODC' := (forall A R, @ODC_on' A R).

Section LS_theorem.

    Definition a_coutable_model M :=
        exists f: nat -> M, surjective f.

    Definition LS_countable :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), a_coutable_model N /\ (exists h: N -> M, N ⪳[h] M /\ exists n: N, h n = m).

    (* Since we need a powerful version of bijective for definiing the predicate over the coutable type *)
    Definition bijective_comp {X Y} :=
        exists f g, (forall x: X, g (f x) = x) /\ forall y: Y, f (g y) = y.

    Definition LS_countable_comp :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), @bijective_comp N nat /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

    Definition LS_term :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: Type) (i_M: interp M), forall m,
            exists (N: interp term), (exists h: term -> M, (forall phi (ρ: env term), ρ ⊨ phi <-> (ρ >> h) ⊨ phi) /\ exists n: term, h n = m).

End LS_theorem.

Goal ODC' -> DP_ω.
Proof.
    intros H A P [].
    destruct (H A (fun x => P) X).
    exists x.
    destruct H0.
    intro H'.
    apply (H1 0).
    intro m.
    exact (H' (S m)).
Qed.



(* A normal version of IP *)
    Definition IndependenceOfGeneralPremises :=
        forall (A:Type) (P:A -> Prop) (Q:Prop),
            inhabited A ->
                (Q -> exists x, P x) -> exists x, Q -> P x.
(* If the results can only be narrowed down to a countable set*)
    Definition CIndependenceOfGeneralPremises :=
        forall (A:Type) (P:A -> Prop) (Q:Prop),
            inhabited A ->
                (Q -> exists x, P x) -> exists (f: nat -> A), Q -> (exists m, P (f m)).

                

(* Then CIndependenceOfGeneralPremises <-> CSDP (Countable version of SDP)
    Definition SDP_ω_on' A (P: A -> Prop) :=
        inhabited A -> 
            exists f: nat -> A, (exists x, P x) -> (exists n, P (f n)).
*)


(* 
Goal (forall A P, @SDP_ω_on' A P)-> IndependenceOfGeneralPremises.
Proof.
    intros.
    intros A P Q IA HP.
    destruct (H A P IA).
    exists x; intros Q'%HP.
    now apply H0.
Qed.

Goal IndependenceOfGeneralPremises -> (forall A P, @SDP_ω_on' A P).
Proof.
    intros.
    intros IA.
    destruct (H A P (exists x, P x) IA).
    easy.
    now exists x.
Qed.


Definition CIndependenceOfGeneralPremises :=
    forall (A:Type) (P:A -> Prop) (Q:Prop),
      inhabited A ->
        (exists f, Q -> forall m: nat, P (f m)) -> (forall x, P x -> Q). *)
    










